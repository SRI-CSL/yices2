/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * MODEL GENERALIZATION
 *
 * Given a model mdl for a formula F(x, y), this module computes
 * the generalization of mdl for the variables 'x'. The result
 * is a formula G(x) such that 
 * 1) G(x) is true in mdl
 * 2) G(x) implies (EXISTS y: F(x, y))
 *
 * If any variable in y is an arithmetic variable then G(x) is
 * computed using model-based projection. Otherwise, G(x) is
 * obtained by substitution: we replace every variable y_i
 * by its value in the model.
 *
 * NOTE: we could use model-based projection in both cases, but
 * experiments with the exists/forall solver seem to show that
 * substitution works better for Boolean and bitvector variables.
 *
 *
 * Two projection variants are implemented:
 *
 * - "local" (gen_model_by_proj_local): the legacy pipeline.
 *   Builds a single literal implicant of f[] at the model
 *   (one literal per disjunction) and projects that flat
 *   conjunction. Cheaper per call but commits to one disjunct,
 *   so the resulting cell is sign-invariant for the chosen
 *   implicant and is often narrower than the wide cell when F
 *   has Boolean structure the model satisfies in more than one
 *   way (it is never broader).
 *
 * - "wide" (gen_model_by_proj_sat_guided): the SAT-guided
 *   enumerator, exposed publicly via YICES_GEN_BY_PROJ_WIDE.
 *   This is an opt-in mode; neither YICES_GEN_BY_PROJ nor
 *   YICES_GEN_DEFAULT select it implicitly.
 *   Builds a model-pruned Boolean abstraction of f[], enumerates
 *   model-true Boolean implicants with a SAT solver and blocker
 *   clauses, projects each implicant as a cube through the legacy
 *   implicant-then-project pipeline, and unions the results at the
 *   term level.
 *   The per-cube get_implicant call in that legacy pipeline is not
 *   used because the SAT-guided cube is suspected not to be an
 *   implicant. It is retained to reuse the existing branch/literal
 *   normalization that project_literals currently expects, instead of
 *   duplicating that cleanup in the WIDE path.
 *
 *   The abstraction is *model-pruned*: every Boolean subterm of F
 *   is evaluated at the model up front, and model-false subterms are
 *   replaced by FALSE in the DAG (which AND simplifies away wherever
 *   they appear under a satisfied disjunction). Only model-true
 *   subterms are recursed into for Boolean structure. As a result
 *   the SAT enumerator only ever sees an abstraction of the part of
 *   F that the model satisfies. The dual precondition violations
 *   (F evaluates to false at the model; F is not even model-evaluable)
 *   are detected separately, see gen_model_by_proj_sat_guided.
 *
 *   On a per-cube projection error (a literal contains a term-kind
 *   the projector does not support) the failing cube is skipped:
 *   its implicant is added as a blocker and SAT enumeration continues
 *   with a different implicant of F.
 *
 *   cube_budget caps the number of distinct normalized cubes attempted
 *   for projection. cube_budget == 0 means unbounded -- the Boolean
 *   enumeration is finite (each iteration adds a blocker clause that
 *   forbids at least one assignment of the abstraction). The cap
 *   deliberately counts attempts rather than successful projections so
 *   that an input whose every implicant uses an unsupported literal
 *   cannot force the loop through all 2^N assignments.
 *
 *   If the cap is hit with at least one success, the result is the
 *   collected projected cubes. If no cube projects successfully, the
 *   wide path falls back to the local cell.
 */

#include <assert.h>

#include "model/generalization.h"
#include "model/model_eval.h"
#include "model/model_queries.h"
#include "model/projection.h"
#include "model/projection_preprocess.h"
#include "model/val_to_term.h"
#include "solvers/cdcl/smt_core.h"
#include "terms/term_manager.h"
#include "terms/term_substitution.h"
#include "terms/terms.h"
#include "utils/int_array_hsets.h"
#include "utils/int_array_sort.h"
#include "utils/int_hash_map.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"


/*
 * Split the array of variables v into discrete and real variables
 * - n = number of variables in v
 * - all variables of type REAL are added to vector reals
 * - all other variables are added to discretes
 */
static void split_elim_array(term_table_t *terms, uint32_t n, const term_t v[], ivector_t *reals, ivector_t *discretes) {
  uint32_t i;
  term_t t;

  for (i=0; i<n; i++) {
    t = v[i];
    if (is_real_term(terms, t)) {
      ivector_push(reals, t);
    } else {
      ivector_push(discretes, t);
    }
  }
}


/*
 * Conversion of error codes to GEN.. codes
 * - eval_errors are in the range [-7 ... -2]
 *   MDL_EVAL_FAILED = -7 and MDL_EVAL_INTERNAL_ERROR = -2
 *   they are kept unchanged
 * - conversion errors are in the range [-6 .. -2]
 *   CONVERT_FAILED = -6 and CONVERT_INTERNAL_ERROR = -2
 *   we renumber them to [-13 .. -9]
 * - implicant construction errors are in the range [-8 ... -2]
 *   MDL_EVAL_FORMULA_FALSE = -8 and MDL_EVAL_INTERNAL_ERROR = -2
 * - projection errors are in the range [-7 .. - 1]
 *   we renumber to [-20 .. -14]
 */
static inline int32_t gen_eval_error(int32_t error) {
  assert(MDL_EVAL_FAILED <= error && error <= MDL_EVAL_INTERNAL_ERROR);
  return error;
}

static inline int32_t gen_convert_error(int32_t error) {
  assert(CONVERT_FAILED <= error && error <= CONVERT_INTERNAL_ERROR);
  return error + (GEN_CONV_INTERNAL_ERROR - CONVERT_INTERNAL_ERROR);
}

static inline int32_t gen_implicant_error(int32_t error) {
  assert(MDL_EVAL_FORMULA_FALSE <= error && error <= MDL_EVAL_INTERNAL_ERROR);
  return error;
}

static inline int32_t gen_projection_error(proj_flag_t error) {
  assert(PROJ_ERROR_UNSUPPORTED_ARITH_TERM <= error && error <= PROJ_ERROR_NON_LINEAR);
  return error + (GEN_PROJ_ERROR_NON_LINEAR - PROJ_ERROR_NON_LINEAR);
}


/*
 * Generalization by substitution: core procedure
 * - mdl = model
 * - mngr = relevant term manager
 * - elim[0 ... nelim -1] = variables to eliminate
 * - on entry to the function, v must contain the formulas to project
 * - the result is returned in place (in vector v)
 *
 * - returned code: 0 if no error, an error code otherwise
 * - error codes are listed in generalization.h
 */
static int32_t gen_model_by_subst(model_t *mdl, term_manager_t *mngr, uint32_t nelims, const term_t elim[], ivector_t *v) {
  term_subst_t subst;
  ivector_t aux;
  term_table_t *terms;
  int32_t code;
  uint32_t k, n;
  term_t t;

  // get the value of elim[i] in aux.data[i]
  init_ivector(&aux, nelims);
  code = evaluate_term_array(mdl, nelims, elim, aux.data);
  if (code < 0) {
    // error in evaluator
    code = gen_eval_error(code);
    assert(GEN_EVAL_FAILED <= code  && code <= GEN_EVAL_INTERNAL_ERROR);
    goto done;
  }

  // convert every aux.data[i] to a constant term
  terms = term_manager_get_terms(mngr);
  k = convert_value_array(mngr, terms, model_get_vtbl(mdl), nelims, aux.data);
  if (k < nelims) {
    // aux.data[k] couldn't be converted to a term
    // the error code is in aux.data[k]
    code = gen_convert_error(aux.data[k]);
    assert(GEN_CONV_FAILED <= code && code <= GEN_CONV_INTERNAL_ERROR);
    goto done;
  }

  // build the substitution: elim[i] := aux.data[i]
  // then apply it to every term in vector v
  code = 0;
  init_term_subst(&subst, mngr, nelims, elim, aux.data);
  n = v->size;
  for (k=0; k<n; k++) {
    t = apply_term_subst(&subst, v->data[k]);
    v->data[k] = t;
    if (t < 0) {
      code = GEN_PROJ_ERROR_IN_SUBST;
      break;
    }
  }
  delete_term_subst(&subst);

 done:
  delete_ivector(&aux);

  return code;
}


static proj_flag_t project_literals_with_extra_elims(model_t *mdl, term_manager_t *mngr,
                                                     uint32_t n, const term_t lits[],
                                                     uint32_t nelims, const term_t elim[],
                                                     const ivector_t *fresh_elims,
                                                     ivector_t *v, int32_t *extra_error) {
  ivector_t all_elims;
  proj_flag_t pflag;

  if (fresh_elims == NULL || fresh_elims->size == 0) {
    return project_literals(mdl, mngr, n, lits, nelims, elim, v, extra_error);
  }

  init_ivector(&all_elims, nelims + fresh_elims->size);
  ivector_add(&all_elims, elim, nelims);
  ivector_add(&all_elims, fresh_elims->data, fresh_elims->size);

  pflag = project_literals(mdl, mngr, n, lits, all_elims.size, all_elims.data, v, extra_error);
  delete_ivector(&all_elims);

  return pflag;
}


/*
 * Generalization by local projection (legacy pipeline):
 *   - compute an implicant of v then project the implicant
 * - mdl = model
 * - mngr = relevant term manager
 * - elim[0 ... nelims-1] = variables to eliminate
 * - on entry to the function, v must contain the formulas to project
 *   the result is returned in place (in vector v)
 * - extra_error = to store another error code for diagnosis (see projection.h).
 *
 * Return code: 0 if no error, an error code otherwise
 *
 * The output cell is sign-invariant for the chosen implicant. If v[]
 * has Boolean structure (disjunctions, Boolean ITEs), only one branch
 * is captured: the one selected by get_implicant from the model.
 */
static int32_t gen_model_by_proj_local_with_cache(model_t *mdl, term_manager_t *mngr,
                                                  uint32_t nelims, const term_t elim[],
                                                  ivector_t *v, int32_t *extra_error,
                                                  arith_construct_preprocess_cache_t *construct_cache,
                                                  rdiv_preprocess_cache_t *rdiv_cache) {
  ivector_t abs_input, implicant, construct_preprocessed, fresh_elims, preprocessed;
  evaluator_t eval;
  int32_t code;
  proj_flag_t pflag;
  bool eval_initialized;

  init_ivector(&abs_input, v->size);
  init_ivector(&implicant, 10);
  init_ivector(&construct_preprocessed, 10);
  init_ivector(&fresh_elims, 0);
  init_ivector(&preprocessed, 10);
  eval_initialized = false;

  pflag = preprocess_abs_terms(mngr, v->size, v->data, &abs_input, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto done;
  }

  code = get_implicant(mdl, mngr, LIT_COLLECTOR_ALL_OPTIONS, abs_input.size, abs_input.data, &implicant);
  if (code < 0) {
    // implicant construction failed
    code = gen_implicant_error(code);
    goto done;
  }

  init_evaluator(&eval, mdl);
  eval_initialized = true;

  pflag = preprocess_arith_construct_literals(construct_cache, &eval,
                                              implicant.size, implicant.data,
                                              &construct_preprocessed, &fresh_elims, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto done;
  }

  pflag = preprocess_rdiv_literals(rdiv_cache, &eval,
                                   construct_preprocessed.size, construct_preprocessed.data,
                                   &preprocessed, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto done;
  }

  delete_evaluator(&eval);
  eval_initialized = false;
  
  ivector_reset(v); // reset v to collect the projection result
  code = 0;
  pflag = project_literals_with_extra_elims(mdl, mngr, preprocessed.size, preprocessed.data,
                                            nelims, elim, &fresh_elims, v, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
  }

 done:
  if (eval_initialized) {
    delete_evaluator(&eval);
  }
  delete_ivector(&preprocessed);
  delete_ivector(&fresh_elims);
  delete_ivector(&construct_preprocessed);
  delete_ivector(&implicant);
  delete_ivector(&abs_input);

  return code;
  
}

static int32_t gen_model_by_proj_local(model_t *mdl, term_manager_t *mngr,
                                       uint32_t nelims, const term_t elim[],
                                       ivector_t *v, int32_t *extra_error) {
  arith_construct_preprocess_cache_t *construct_cache;
  rdiv_preprocess_cache_t *rdiv_cache;
  int32_t code;

  construct_cache = new_arith_construct_preprocess_cache(mdl, mngr);
  rdiv_cache = new_rdiv_preprocess_cache(mdl, mngr);
  code = gen_model_by_proj_local_with_cache(mdl, mngr, nelims, elim, v, extra_error,
                                            construct_cache, rdiv_cache);
  delete_rdiv_preprocess_cache(rdiv_cache);
  delete_arith_construct_preprocess_cache(construct_cache);

  return code;
}



/*
 * Project a single SAT-guided cube via the legacy implicant+project
 * pipeline. The cube is expected to be an implicant already; the
 * get_implicant call is kept as a code-reuse boundary for the legacy
 * branch/literal normalization that project_literals currently expects.
 *
 * The projected literals are appended to *out (a list of literals
 * whose AND is the projected cube). out is not reset.
 */
static int32_t project_one_cube_into(model_t *mdl, term_manager_t *mngr,
                                     arith_construct_preprocess_cache_t *construct_cache,
                                     rdiv_preprocess_cache_t *rdiv_cache,
                                     const term_t *cube_lits, uint32_t cube_size,
                                     uint32_t nelims, const term_t elim[],
                                     ivector_t *out, int32_t *extra_error) {
  ivector_t implicant, construct_preprocessed, fresh_elims, preprocessed;
  evaluator_t eval;
  proj_flag_t pflag;
  int32_t code;
  bool eval_initialized;

  init_ivector(&implicant, cube_size);
  init_ivector(&construct_preprocessed, cube_size);
  init_ivector(&fresh_elims, 0);
  init_ivector(&preprocessed, cube_size);
  eval_initialized = false;

  code = get_implicant(mdl, mngr, LIT_COLLECTOR_ALL_OPTIONS, cube_size, cube_lits, &implicant);
  if (code < 0) {
    code = gen_implicant_error(code);
    goto cleanup;
  }

  init_evaluator(&eval, mdl);
  eval_initialized = true;

  pflag = preprocess_arith_construct_literals(construct_cache, &eval,
                                              implicant.size, implicant.data,
                                              &construct_preprocessed, &fresh_elims, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto cleanup;
  }

  pflag = preprocess_rdiv_literals(rdiv_cache, &eval,
                                   construct_preprocessed.size, construct_preprocessed.data,
                                   &preprocessed, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto cleanup;
  }

  delete_evaluator(&eval);
  eval_initialized = false;

  pflag = project_literals_with_extra_elims(mdl, mngr, preprocessed.size, preprocessed.data,
                                            nelims, elim, &fresh_elims, out, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto cleanup;
  }

  code = 0;

 cleanup:
  if (eval_initialized) {
    delete_evaluator(&eval);
  }
  delete_ivector(&preprocessed);
  delete_ivector(&fresh_elims);
  delete_ivector(&construct_preprocessed);
  delete_ivector(&implicant);
  return code;
}


/*
 * SAT-GUIDED WIDE PROJECTION
 *
 * Front end built on a model-pruned Boolean abstraction and SAT-guided
 * implicant enumeration. Each emitted Boolean implicant is mapped back
 * to a theory cube and projected via project_one_cube_into above. The
 * union of the projected cubes is returned as the wide cell.
 */

typedef int32_t bool_node_id_t;

typedef enum {
  BOOL_NODE_TRUE = 0,
  BOOL_NODE_FALSE = 1,
  BOOL_NODE_LIT = 2,
  BOOL_NODE_AND = 3,
  BOOL_NODE_OR = 4,
} bool_node_kind_t;

typedef struct bool_node_s {
  uint8_t kind;
  literal_t lit;
  uint32_t start;
  uint32_t count;
  literal_t tseitin;
} bool_node_t;

typedef struct bool_dag_s {
  bool_node_t *data;
  uint32_t size;
  uint32_t capacity;
  ivector_t children;
} bool_dag_t;

enum {
  BOOL_DAG_TRUE = 0,
  BOOL_DAG_FALSE = 1,
};

typedef enum {
  ABS_OK = 0,
  ABS_ERROR = 1,
} abs_status_t;

typedef enum {
  ABS_EVAL_FALSE = 0,
  ABS_EVAL_TRUE = 1,
  ABS_EVAL_ERROR = 2,
} abs_eval_t;

typedef struct abs_builder_s {
  term_manager_t *mngr;
  term_table_t *terms;
  evaluator_t *eval;
  int_hmap_t lit_to_bvar;
  ivector_t bvar_to_lit;
  int_hmap_t cache_signed;
  bool_dag_t dag;
  uint32_t ite_expansions;
  uint32_t max_ite_expansions;
  bool decomposed;
} abs_builder_t;

static void init_bool_dag(bool_dag_t *dag) {
  dag->capacity = 32;
  dag->size = 0;
  dag->data = (bool_node_t *) safe_malloc(dag->capacity * sizeof(bool_node_t));
  init_ivector(&dag->children, 64);

  // Constant TRUE node.
  dag->data[dag->size].kind = BOOL_NODE_TRUE;
  dag->data[dag->size].lit = null_literal;
  dag->data[dag->size].start = 0;
  dag->data[dag->size].count = 0;
  dag->data[dag->size].tseitin = null_literal;
  dag->size ++;

  // Constant FALSE node.
  dag->data[dag->size].kind = BOOL_NODE_FALSE;
  dag->data[dag->size].lit = null_literal;
  dag->data[dag->size].start = 0;
  dag->data[dag->size].count = 0;
  dag->data[dag->size].tseitin = null_literal;
  dag->size ++;
}

static void delete_bool_dag(bool_dag_t *dag) {
  safe_free(dag->data);
  dag->data = NULL;
  dag->size = 0;
  dag->capacity = 0;
  delete_ivector(&dag->children);
}

static void bool_dag_rollback(bool_dag_t *dag, uint32_t size, uint32_t children_size) {
  assert(BOOL_DAG_FALSE < size && size <= dag->size);
  assert(children_size <= dag->children.size);

  dag->size = size;
  dag->children.size = children_size;
}

static bool_node_id_t bool_dag_add_node(bool_dag_t *dag, bool_node_kind_t kind,
                                        literal_t lit, uint32_t n, const int32_t child[]) {
  bool_node_id_t id;
  uint32_t i;

  if (dag->size == dag->capacity) {
    dag->capacity <<= 1;
    dag->data = (bool_node_t *) safe_realloc(dag->data, dag->capacity * sizeof(bool_node_t));
  }

  id = (bool_node_id_t) dag->size;
  dag->data[id].kind = kind;
  dag->data[id].lit = lit;
  dag->data[id].start = dag->children.size;
  dag->data[id].count = n;
  dag->data[id].tseitin = null_literal;
  for (i = 0; i < n; i++) {
    ivector_push(&dag->children, child[i]);
  }
  dag->size ++;
  return id;
}

static bool_node_id_t bool_dag_add_lit(bool_dag_t *dag, literal_t lit) {
  return bool_dag_add_node(dag, BOOL_NODE_LIT, lit, 0, NULL);
}

static bool_node_id_t bool_dag_add_and(bool_dag_t *dag, uint32_t n, const int32_t child[]) {
  return bool_dag_add_node(dag, BOOL_NODE_AND, null_literal, n, child);
}

static bool_node_id_t bool_dag_add_or(bool_dag_t *dag, uint32_t n, const int32_t child[]) {
  return bool_dag_add_node(dag, BOOL_NODE_OR, null_literal, n, child);
}

static inline bool bool_node_is_true(bool_node_id_t id) {
  return id == BOOL_DAG_TRUE;
}

static inline bool bool_node_is_false(bool_node_id_t id) {
  return id == BOOL_DAG_FALSE;
}

static void init_abs_builder(abs_builder_t *b, model_t *mdl, term_manager_t *mngr,
                             evaluator_t *eval, uint32_t max_ite_expansions) {
  b->mngr = mngr;
  b->terms = term_manager_get_terms(mngr);
  b->eval = eval;
  init_int_hmap(&b->lit_to_bvar, 0);
  init_ivector(&b->bvar_to_lit, 16);
  ivector_push(&b->bvar_to_lit, NULL_TERM); // var 0 is reserved by the Boolean solvers
  init_int_hmap(&b->cache_signed, 0);
  init_bool_dag(&b->dag);
  b->ite_expansions = 0;
  b->max_ite_expansions = max_ite_expansions;
  b->decomposed = false;
  (void) mdl;
}

static void delete_abs_builder(abs_builder_t *b) {
  // After ABS_ERROR, discard the whole builder: rollback does not undo caches.
  delete_bool_dag(&b->dag);
  delete_int_hmap(&b->cache_signed);
  delete_ivector(&b->bvar_to_lit);
  delete_int_hmap(&b->lit_to_bvar);
}

static bvar_t abs_builder_get_lit_var(abs_builder_t *b, term_t lit) {
  int_hmap_pair_t *r;
  bvar_t v;

  r = int_hmap_get(&b->lit_to_bvar, lit);
  if (r->val < 0) {
    v = (bvar_t) b->bvar_to_lit.size;
    r->val = v;
    ivector_push(&b->bvar_to_lit, lit);
  } else {
    v = (bvar_t) r->val;
  }
  return v;
}

static abs_status_t abstract_signed(abs_builder_t *b, term_t t, bool_node_id_t *out);

static void ivector_push_unique(ivector_t *v, int32_t x) {
  uint32_t i, n;

  n = v->size;
  for (i = 0; i < n; i++) {
    if (v->data[i] == x) {
      return;
    }
  }
  ivector_push(v, x);
}

static abs_status_t bool_dag_mk_and(abs_builder_t *b, ivector_t *child, bool_node_id_t *out) {
  bool_dag_t *dag;
  ivector_t flat;
  uint32_t i, j, n;
  bool_node_id_t id;
  bool_node_t *node;

  dag = &b->dag;
  init_ivector(&flat, child->size);
  n = child->size;
  for (i = 0; i < n; i++) {
    id = child->data[i];
    if (bool_node_is_false(id)) {
      *out = BOOL_DAG_FALSE;
      delete_ivector(&flat);
      return ABS_OK;
    }
    if (bool_node_is_true(id)) {
      continue;
    }
    node = &dag->data[id];
    if (node->kind == BOOL_NODE_AND) {
      for (j = 0; j < node->count; j++) {
        ivector_push_unique(&flat, dag->children.data[node->start + j]);
      }
    } else {
      ivector_push_unique(&flat, id);
    }
  }

  if (flat.size == 0) {
    *out = BOOL_DAG_TRUE;
  } else if (flat.size == 1) {
    *out = flat.data[0];
  } else {
    *out = bool_dag_add_and(dag, flat.size, flat.data);
  }
  delete_ivector(&flat);
  return ABS_OK;
}

static abs_status_t bool_dag_mk_or(abs_builder_t *b, ivector_t *child, bool_node_id_t *out) {
  bool_dag_t *dag;
  ivector_t flat;
  uint32_t i, j, n;
  bool_node_id_t id;
  bool_node_t *node;

  dag = &b->dag;
  init_ivector(&flat, child->size);
  n = child->size;
  for (i = 0; i < n; i++) {
    id = child->data[i];
    if (bool_node_is_true(id)) {
      *out = BOOL_DAG_TRUE;
      delete_ivector(&flat);
      return ABS_OK;
    }
    if (bool_node_is_false(id)) {
      continue;
    }
    node = &dag->data[id];
    if (node->kind == BOOL_NODE_OR) {
      for (j = 0; j < node->count; j++) {
        ivector_push_unique(&flat, dag->children.data[node->start + j]);
      }
    } else {
      ivector_push_unique(&flat, id);
    }
  }

  if (flat.size == 0) {
    *out = BOOL_DAG_FALSE;
  } else if (flat.size == 1) {
    *out = flat.data[0];
  } else {
    *out = bool_dag_add_or(dag, flat.size, flat.data);
  }
  delete_ivector(&flat);
  return ABS_OK;
}

static abs_status_t abstract_or_term(abs_builder_t *b, composite_term_t *desc, bool_node_id_t *out) {
  ivector_t child;
  uint32_t i, n;
  bool_node_id_t c;
  abs_status_t st;

  n = desc->arity;
  init_ivector(&child, n);
  for (i = 0; i < n; i++) {
    st = abstract_signed(b, desc->arg[i], &c);
    if (st != ABS_OK) {
      delete_ivector(&child);
      return st;
    }
    ivector_push(&child, c);
  }
  st = bool_dag_mk_or(b, &child, out);
  delete_ivector(&child);
  return st;
}

static abs_status_t abstract_and_of_opposites(abs_builder_t *b, composite_term_t *desc, bool_node_id_t *out) {
  ivector_t child;
  uint32_t i, n;
  bool_node_id_t c;
  abs_status_t st;

  n = desc->arity;
  init_ivector(&child, n);
  for (i = 0; i < n; i++) {
    st = abstract_signed(b, opposite_term(desc->arg[i]), &c);
    if (st != ABS_OK) {
      delete_ivector(&child);
      return st;
    }
    ivector_push(&child, c);
    if (bool_node_is_false(c)) {
      break;
    }
  }
  st = bool_dag_mk_and(b, &child, out);
  delete_ivector(&child);
  return st;
}

static abs_status_t abstract_and2(abs_builder_t *b, term_t a, term_t c, bool_node_id_t *out) {
  ivector_t child;
  bool_node_id_t x;
  abs_status_t st;

  init_ivector(&child, 2);
  st = abstract_signed(b, a, &x);
  if (st != ABS_OK) goto done;
  ivector_push(&child, x);
  if (! bool_node_is_false(x)) {
    st = abstract_signed(b, c, &x);
    if (st != ABS_OK) goto done;
    ivector_push(&child, x);
  }
  st = bool_dag_mk_and(b, &child, out);

 done:
  delete_ivector(&child);
  return st;
}

static bool find_ite_subterm_in_term(abs_builder_t *b, term_t t, term_t *ite);

static bool find_ite_subterm_in_pprod(abs_builder_t *b, pprod_t *p, term_t *ite) {
  uint32_t i, n;

  if (p == empty_pp || has_int_tag(p)) {
    return false;
  }

  n = p->len;
  for (i = 0; i < n; i++) {
    if (find_ite_subterm_in_term(b, p->prod[i].var, ite)) {
      return true;
    }
  }
  return false;
}

static bool find_ite_subterm_in_poly(abs_builder_t *b, polynomial_t *p, term_t *ite) {
  uint32_t i, n;
  term_t t;

  n = p->nterms;
  for (i = 0; i < n; i++) {
    t = p->mono[i].var;
    if (t != const_idx && find_ite_subterm_in_term(b, t, ite)) {
      return true;
    }
  }
  return false;
}

static bool find_ite_subterm_in_composite(abs_builder_t *b, composite_term_t *d, term_t *ite) {
  uint32_t i, n;

  n = d->arity;
  for (i = 0; i < n; i++) {
    if (find_ite_subterm_in_term(b, d->arg[i], ite)) {
      return true;
    }
  }
  return false;
}

static bool find_ite_subterm_in_term(abs_builder_t *b, term_t t, term_t *ite) {
  term_t base;
  term_kind_t kind;

  if (t < 0) {
    t = unsigned_term(t);
  }
  if (t < 0) {
    return false;
  }

  base = t;
  kind = term_kind(b->terms, base);
  if (kind == ITE_TERM || kind == ITE_SPECIAL) {
    *ite = base;
    return true;
  }

  switch (kind) {
  case ARITH_EQ_ATOM:
    return find_ite_subterm_in_term(b, arith_eq_arg(b->terms, base), ite);
  case ARITH_GE_ATOM:
    return find_ite_subterm_in_term(b, arith_ge_arg(b->terms, base), ite);
  case EQ_TERM:
  case DISTINCT_TERM:
  case OR_TERM:
  case XOR_TERM:
  case ARITH_BINEQ_ATOM:
  case ARITH_RDIV:
  case ARITH_IDIV:
  case ARITH_MOD:
  case BV_EQ_ATOM:
    return find_ite_subterm_in_composite(b, composite_term_desc(b->terms, base), ite);
  case POWER_PRODUCT:
    return find_ite_subterm_in_pprod(b, pprod_term_desc(b->terms, base), ite);
  case ARITH_POLY:
    return find_ite_subterm_in_poly(b, poly_term_desc(b->terms, base), ite);
  default:
    return false;
  }
}

static term_t replace_ite_subterm(abs_builder_t *b, term_t t, term_t from, term_t to, bool *ok);

static bool replace_ite_subterm_in_children(abs_builder_t *b, composite_term_t *d, term_t from, term_t to, bool *ok, term_t a[]) {
  uint32_t i, n;

  n = d->arity;
  for (i = 0; i < n; i++) {
    a[i] = replace_ite_subterm(b, d->arg[i], from, to, ok);
    if (! *ok || a[i] == NULL_TERM) {
      return false;
    }
  }
  return true;
}

static term_t replace_ite_subterm_in_pprod(abs_builder_t *b, pprod_t *p, term_t from, term_t to, bool *ok) {
  term_t *a;
  term_t r;
  uint32_t i, n;

  if (p == empty_pp || has_int_tag(p)) {
    return pprod_term(b->terms, p);
  }

  n = p->len;
  a = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i = 0; i < n; i++) {
    a[i] = replace_ite_subterm(b, p->prod[i].var, from, to, ok);
    if (! *ok || a[i] == NULL_TERM) {
      safe_free(a);
      return NULL_TERM;
    }
  }

  r = mk_pprod(b->mngr, p, n, a);
  safe_free(a);
  if (r == NULL_TERM) {
    *ok = false;
  }
  return r;
}

static term_t replace_ite_subterm_in_poly(abs_builder_t *b, polynomial_t *p, term_t from, term_t to, bool *ok) {
  term_t *a;
  term_t r;
  uint32_t i, n;

  n = p->nterms;
  a = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i = 0; i < n; i++) {
    if (p->mono[i].var == const_idx) {
      a[i] = const_idx;
    } else {
      a[i] = replace_ite_subterm(b, p->mono[i].var, from, to, ok);
      if (! *ok || a[i] == NULL_TERM) {
        safe_free(a);
        return NULL_TERM;
      }
    }
  }

  r = mk_arith_poly(b->mngr, p, n, a);
  safe_free(a);
  if (r == NULL_TERM) {
    *ok = false;
  }
  return r;
}

static term_t replace_ite_subterm(abs_builder_t *b, term_t t, term_t from, term_t to, bool *ok) {
  term_t base, result;
  term_t *a;
  composite_term_t *d;
  term_kind_t kind;
  bool neg;

  if (! *ok) {
    return NULL_TERM;
  }
  if (t == from) {
    return to;
  }
  if (t < 0 && unsigned_term(t) == from) {
    if (is_boolean_term(b->terms, to)) {
      return opposite_term(to);
    }
    *ok = false;
    return NULL_TERM;
  }
  if (t < 0) {
    base = unsigned_term(t);
    neg = true;
  } else {
    base = t;
    neg = false;
  }
  if (base < 0) {
    return t;
  }

  kind = term_kind(b->terms, base);
  switch (kind) {
  case ITE_TERM:
  case ITE_SPECIAL:
    d = ite_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_ite(b->mngr, a[0], a[1], a[2], term_type(b->terms, base));
    safe_free(a);
    break;

  case ARITH_EQ_ATOM:
    result = mk_arith_term_eq0(b->mngr, replace_ite_subterm(b, arith_eq_arg(b->terms, base), from, to, ok));
    break;

  case ARITH_GE_ATOM:
    result = mk_arith_term_geq0(b->mngr, replace_ite_subterm(b, arith_ge_arg(b->terms, base), from, to, ok));
    break;

  case EQ_TERM:
    d = eq_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_eq(b->mngr, a[0], a[1]);
    safe_free(a);
    break;

  case DISTINCT_TERM:
    d = distinct_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_distinct(b->mngr, d->arity, a);
    safe_free(a);
    break;

  case OR_TERM:
    d = or_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_or_safe(b->mngr, d->arity, a);
    safe_free(a);
    break;

  case XOR_TERM:
    d = xor_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_xor_safe(b->mngr, d->arity, a);
    safe_free(a);
    break;

  case ARITH_BINEQ_ATOM:
    d = arith_bineq_atom_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_arith_eq(b->mngr, a[0], a[1]);
    safe_free(a);
    break;

  case ARITH_RDIV:
    d = arith_rdiv_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_arith_rdiv(b->mngr, a[0], a[1]);
    safe_free(a);
    break;

  case ARITH_IDIV:
    d = arith_idiv_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_arith_idiv(b->mngr, a[0], a[1]);
    safe_free(a);
    break;

  case ARITH_MOD:
    d = arith_mod_term_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_arith_mod(b->mngr, a[0], a[1]);
    safe_free(a);
    break;

  case BV_EQ_ATOM:
    d = bveq_atom_desc(b->terms, base);
    a = (term_t *) safe_malloc(d->arity * sizeof(term_t));
    if (! replace_ite_subterm_in_children(b, d, from, to, ok, a)) {
      safe_free(a);
      return NULL_TERM;
    }
    result = mk_bveq(b->mngr, a[0], a[1]);
    safe_free(a);
    break;

  case POWER_PRODUCT:
    result = replace_ite_subterm_in_pprod(b, pprod_term_desc(b->terms, base), from, to, ok);
    break;

  case ARITH_POLY:
    result = replace_ite_subterm_in_poly(b, poly_term_desc(b->terms, base), from, to, ok);
    break;

  default:
    result = t;
    break;
  }

  if (! *ok || result == NULL_TERM) {
    *ok = false;
    return NULL_TERM;
  }
  return neg ? opposite_term(result) : result;
}

static bool try_build_ite_branch_terms(abs_builder_t *b, term_t t, term_t ite,
                                       term_t *cond, term_t *then_t, term_t *else_t) {
  composite_term_t *d;
  term_t base, then_base, else_base;
  bool ok;

  d = ite_term_desc(b->terms, ite);
  base = unsigned_term(t);
  ok = true;
  then_base = replace_ite_subterm(b, base, ite, d->arg[1], &ok);
  if (! ok || then_base == NULL_TERM) {
    return false;
  }
  ok = true;
  else_base = replace_ite_subterm(b, base, ite, d->arg[2], &ok);
  if (! ok || else_base == NULL_TERM) {
    return false;
  }

  *cond = d->arg[0];
  *then_t = is_neg_term(t) ? opposite_term(then_base) : then_base;
  *else_t = is_neg_term(t) ? opposite_term(else_base) : else_base;
  return true;
}

static bool abs_builder_can_expand_ite(abs_builder_t *b) {
  return b->max_ite_expansions == 0 || b->ite_expansions < b->max_ite_expansions;
}

static bool abstract_ite_in_leaf(abs_builder_t *b, term_t t, bool_node_id_t *out, abs_status_t *status) {
  term_t ite, cond, then_t, else_t;
  bool_node_id_t left, right, both;
  ivector_t child;
  abs_status_t st;

  if (! abs_builder_can_expand_ite(b) ||
      ! find_ite_subterm_in_term(b, unsigned_term(t), &ite)) {
    return false;
  }
  if (! try_build_ite_branch_terms(b, t, ite, &cond, &then_t, &else_t)) {
    return false;
  }

  b->ite_expansions ++;
  b->decomposed = true;

  st = abstract_and2(b, cond, then_t, &left);
  if (st != ABS_OK) goto done_no_vector;

  st = abstract_and2(b, opposite_term(cond), else_t, &right);
  if (st != ABS_OK) goto done_no_vector;

  st = abstract_and2(b, then_t, else_t, &both);
  if (st != ABS_OK) goto done_no_vector;

  init_ivector(&child, 3);
  ivector_push(&child, left);
  ivector_push(&child, right);
  ivector_push(&child, both);
  st = bool_dag_mk_or(b, &child, out);
  delete_ivector(&child);

 done_no_vector:
  *status = st;
  return true;
}

static abs_status_t abstract_boolean_ite(abs_builder_t *b, term_t base, bool neg, bool_node_id_t *out) {
  composite_term_t *idesc;
  term_t cond, then_b, else_b;
  bool_node_id_t left, right, both;
  ivector_t child;
  abs_status_t st;

  idesc = ite_term_desc(b->terms, base);
  cond = idesc->arg[0];
  then_b = idesc->arg[1];
  else_b = idesc->arg[2];

  st = abstract_and2(b, cond, neg ? opposite_term(then_b) : then_b, &left);
  if (st != ABS_OK) return st;

  st = abstract_and2(b, opposite_term(cond), neg ? opposite_term(else_b) : else_b, &right);
  if (st != ABS_OK) return st;

  st = abstract_and2(b, neg ? opposite_term(then_b) : then_b,
                     neg ? opposite_term(else_b) : else_b, &both);
  if (st != ABS_OK) return st;

  init_ivector(&child, 3);
  ivector_push(&child, left);
  ivector_push(&child, right);
  ivector_push(&child, both);
  st = bool_dag_mk_or(b, &child, out);
  delete_ivector(&child);
  return st;
}

static abs_status_t abstract_leaf(abs_builder_t *b, term_t t, bool_node_id_t *out) {
  bvar_t v;

  v = abs_builder_get_lit_var(b, t);
  *out = bool_dag_add_lit(&b->dag, pos_lit(v));
  return ABS_OK;
}

static abs_eval_t eval_boolean_at_model(evaluator_t *eval, term_t t) {
  value_t v;

  v = eval_in_model(eval, t);
  if (! good_object(eval->vtbl, v) || ! object_is_boolean(eval->vtbl, v)) {
    return ABS_EVAL_ERROR;
  }
  return boolobj_value(eval->vtbl, v) ? ABS_EVAL_TRUE : ABS_EVAL_FALSE;
}

static abs_status_t abstract_signed(abs_builder_t *b, term_t t, bool_node_id_t *out) {
  int_hmap_pair_t *r;
  term_t base;
  bool neg;
  term_kind_t kind;
  uint32_t saved_dag_size, saved_children_size;
  abs_eval_t eval;
  abs_status_t st;

  r = int_hmap_find(&b->cache_signed, t);
  if (r != NULL) {
    *out = r->val;
    return ABS_OK;
  }

  if (t == true_term) {
    *out = BOOL_DAG_TRUE;
    goto cache_result;
  }
  if (t == false_term) {
    *out = BOOL_DAG_FALSE;
    goto cache_result;
  }

  eval = eval_boolean_at_model(b->eval, t);
  if (eval == ABS_EVAL_ERROR) {
    return ABS_ERROR;
  }
  if (eval == ABS_EVAL_FALSE) {
    *out = BOOL_DAG_FALSE;
  } else {
    saved_dag_size = b->dag.size;
    saved_children_size = b->dag.children.size;

    base = unsigned_term(t);
    neg = is_neg_term(t);
    kind = term_kind(b->terms, base);

    if (kind == OR_TERM) {
      b->decomposed = true;
      if (neg) {
        st = abstract_and_of_opposites(b, or_term_desc(b->terms, base), out);
      } else {
        st = abstract_or_term(b, or_term_desc(b->terms, base), out);
      }
      if (st != ABS_OK) goto error;
      goto cache_result;
    }

    if ((kind == ITE_TERM || kind == ITE_SPECIAL) && is_boolean_term(b->terms, base) &&
        abs_builder_can_expand_ite(b)) {
      b->ite_expansions ++;
      b->decomposed = true;
      st = abstract_boolean_ite(b, base, neg, out);
      if (st != ABS_OK) goto error;
      goto cache_result;
    }

    if (abstract_ite_in_leaf(b, t, out, &st)) {
      if (st != ABS_OK) goto error;
      goto cache_result;
    }

    (void) abstract_leaf(b, t, out);
  }

 cache_result:
  int_hmap_add(&b->cache_signed, t, *out);
  return ABS_OK;

 error:
  // Roll back only the DAG; successful subcalls may have populated caches.
  // The caller must discard this builder after ABS_ERROR.
  bool_dag_rollback(&b->dag, saved_dag_size, saved_children_size);
  return st;
}

static abs_status_t abstract_formula_array(abs_builder_t *b, uint32_t n, const term_t f[], bool_node_id_t *out) {
  ivector_t child;
  uint32_t i;
  bool_node_id_t c;
  abs_status_t st;

  init_ivector(&child, n);
  for (i = 0; i < n; i++) {
    st = abstract_signed(b, f[i], &c);
    if (st != ABS_OK) {
      delete_ivector(&child);
      return st;
    }
    ivector_push(&child, c);
    if (bool_node_is_false(c)) {
      break;
    }
  }
  st = bool_dag_mk_and(b, &child, out);
  delete_ivector(&child);
  return st;
}

static void bool_dag_reset_tseitin(bool_dag_t *dag);

/*
 * Minimal no-theory interface for a Boolean-only SMT core.
 */
static void gen_bool_donothing(void *solver) {
}

static void gen_bool_backtrack(void *solver, uint32_t backlevel) {
}

static bool gen_bool_propagate(void *solver) {
  return true;
}

static fcheck_code_t gen_bool_final_check(void *solver) {
  return FCHECK_SAT;
}

static th_ctrl_interface_t gen_bool_ctrl = {
  gen_bool_donothing,     // start_internalization
  gen_bool_donothing,     // start_search
  gen_bool_propagate,     // propagate
  gen_bool_final_check,   // final check
  gen_bool_donothing,     // increase_decision_level
  gen_bool_backtrack,     // backtrack
  gen_bool_donothing,     // push
  gen_bool_donothing,     // pop
  gen_bool_donothing,     // reset
  gen_bool_donothing,     // clear
};

static th_smt_interface_t gen_bool_smt = {
  // The core is always put in bool-only mode before search. These theory-SMT
  // hooks must therefore be unreachable for this enumeration-only solver.
  NULL, NULL, NULL, NULL, NULL,
};

static void core_add_clause(smt_core_t *core, uint32_t n, literal_t *lit) {
  add_clause(core, n, lit);
}

static void core_add_unit_clause(smt_core_t *core, literal_t l) {
  literal_t clause[1];

  clause[0] = l;
  core_add_clause(core, 1, clause);
}

static void core_add_binary_clause(smt_core_t *core, literal_t l1, literal_t l2) {
  literal_t clause[2];

  clause[0] = l1;
  clause[1] = l2;
  core_add_clause(core, 2, clause);
}

static literal_t core_clausify_node(bool_dag_t *dag, smt_core_t *core, bool_node_id_t id) {
  bool_node_t *node;
  literal_t result, child_lit;
  ivector_t clause;
  uint32_t i;

  assert(0 <= id && (uint32_t) id < dag->size);
  node = &dag->data[id];
  if (node->tseitin != null_literal) {
    return node->tseitin;
  }

  switch (node->kind) {
  case BOOL_NODE_LIT:
    result = node->lit;
    break;

  case BOOL_NODE_AND:
    result = pos_lit(create_boolean_variable(core));
    init_ivector(&clause, node->count + 1);
    ivector_push(&clause, result);
    for (i = 0; i < node->count; i++) {
      child_lit = core_clausify_node(dag, core, dag->children.data[node->start + i]);
      core_add_binary_clause(core, not(result), child_lit);
      ivector_push(&clause, not(child_lit));
    }
    core_add_clause(core, clause.size, clause.data);
    delete_ivector(&clause);
    break;

  case BOOL_NODE_OR:
    result = pos_lit(create_boolean_variable(core));
    init_ivector(&clause, node->count + 1);
    ivector_push(&clause, not(result));
    for (i = 0; i < node->count; i++) {
      child_lit = core_clausify_node(dag, core, dag->children.data[node->start + i]);
      core_add_binary_clause(core, not(child_lit), result);
      ivector_push(&clause, child_lit);
    }
    core_add_clause(core, clause.size, clause.data);
    delete_ivector(&clause);
    break;

  default:
    assert(false);
    result = null_literal;
    break;
  }

  node->tseitin = result;
  return result;
}

static smt_status_t bool_core_solve_negative(smt_core_t *core) {
  literal_t l;

  // A blocker can simplify to the empty clause. start_search clears this flag.
  if (core->inconsistent) {
    return YICES_STATUS_UNSAT;
  }

  start_search(core, 0, NULL);
  smt_process(core);
  while (smt_status(core) == YICES_STATUS_SEARCHING) {
    l = select_unassigned_literal(core);
    if (l == null_literal) {
      smt_final_check(core);
    } else {
      decide_literal(core, l | 1); // strict negative polarity
      smt_process(core);
    }
  }
  return smt_status(core);
}

static void normalize_literal_vector(ivector_t *v) {
  uint32_t i, j, n;
  int32_t last;

  n = v->size;
  if (n <= 1) {
    return;
  }
  int_array_sort(v->data, n);
  j = 1;
  last = v->data[0];
  for (i = 1; i < n; i++) {
    if (v->data[i] != last) {
      last = v->data[i];
      v->data[j] = last;
      j ++;
    }
  }
  v->size = j;
}

#ifndef NDEBUG
static bool bool_dag_eval_selected(bool_dag_t *dag, const bool *selected, bool_node_id_t id) {
  bool_node_t *node;
  uint32_t i;

  node = &dag->data[id];
  switch (node->kind) {
  case BOOL_NODE_TRUE:
    return true;
  case BOOL_NODE_FALSE:
    return false;
  case BOOL_NODE_LIT:
    assert(is_pos(node->lit));
    return selected[var_of(node->lit)];
  case BOOL_NODE_AND:
    for (i = 0; i < node->count; i++) {
      if (! bool_dag_eval_selected(dag, selected, dag->children.data[node->start + i])) {
        return false;
      }
    }
    return true;
  case BOOL_NODE_OR:
    for (i = 0; i < node->count; i++) {
      if (bool_dag_eval_selected(dag, selected, dag->children.data[node->start + i])) {
        return true;
      }
    }
    return false;
  default:
    assert(false);
    return false;
  }
}

static void assert_selected_satisfies_root(abs_builder_t *b, bool_node_id_t root, const ivector_t *selected_lits) {
  bool *selected;
  uint32_t i, n;

  n = b->bvar_to_lit.size;
  selected = (bool *) safe_malloc(n * sizeof(bool));
  for (i = 0; i < n; i++) {
    selected[i] = false;
  }
  for (i = 0; i < selected_lits->size; i++) {
    assert(is_pos(selected_lits->data[i]));
    assert(var_of(selected_lits->data[i]) < n);
    selected[var_of(selected_lits->data[i])] = true;
  }
  assert(bool_dag_eval_selected(&b->dag, selected, root));
  safe_free(selected);
}
#endif

static void collect_selected_literals(abs_builder_t *b, smt_core_t *core, ivector_t *selected_lits, ivector_t *cube) {
  uint32_t i, n;
  literal_t lit;

  ivector_reset(selected_lits);
  ivector_reset(cube);
  n = b->bvar_to_lit.size;
  for (i = 1; i < n; i++) {
    lit = pos_lit(i);
    if (literal_value(core, lit) == VAL_TRUE) {
      ivector_push(selected_lits, lit);
      ivector_push(cube, b->bvar_to_lit.data[i]);
    }
  }
}

static void add_superset_blocker_to_core(smt_core_t *core, const ivector_t *selected_lits) {
  ivector_t clause;
  uint32_t i, n;

  n = selected_lits->size;
  init_ivector(&clause, n);
  for (i = 0; i < n; i++) {
    ivector_push(&clause, not(selected_lits->data[i]));
  }
  core_add_clause(core, clause.size, clause.data);
  delete_ivector(&clause);
}

static void init_abstraction_core(abs_builder_t *builder, bool_node_id_t root, smt_core_t *core) {
  literal_t root_lit;

  init_smt_core(core, builder->bvar_to_lit.size + builder->dag.size + 8,
                NULL, &gen_bool_ctrl, &gen_bool_smt, SMT_MODE_BASIC);
  smt_core_set_bool_only(core);
  set_randomness(core, 0.0f);
  add_boolean_variables(core, builder->bvar_to_lit.size - 1);

  bool_dag_reset_tseitin(&builder->dag);
  root_lit = core_clausify_node(&builder->dag, core, root);
  core_add_unit_clause(core, root_lit);
}

typedef struct cube_enum_status_s {
  bool sat_exhausted;
  bool budget_exhausted;
  bool used_local_fallback;
  bool saw_duplicate;
} cube_enum_status_t;

static void init_cube_enum_status(cube_enum_status_t *status) {
  status->sat_exhausted = false;
  status->budget_exhausted = false;
  status->used_local_fallback = false;
  status->saw_duplicate = false;
}

static int32_t add_normalized_implicant_cube(model_t *mdl, term_manager_t *mngr,
                                             uint32_t n, const term_t a[],
                                             int_array_hset_t *seen,
                                             ivector_t *cube_stream, bool *added) {
  ivector_t implicant;
  int32_t code;

  *added = false;
  init_ivector(&implicant, n);
  code = get_implicant(mdl, mngr, LIT_COLLECTOR_ALL_OPTIONS, n, a, &implicant);
  if (code < 0) {
    delete_ivector(&implicant);
    return gen_implicant_error(code);
  }

  normalize_literal_vector(&implicant);
  if (int_array_hset_find(seen, implicant.size, implicant.data) == NULL) {
    int_array_hset_get(seen, implicant.size, implicant.data);
    if (cube_stream->size > 0) {
      ivector_push(cube_stream, NULL_TERM);
    }
    ivector_add(cube_stream, implicant.data, implicant.size);
    *added = true;
  }

  delete_ivector(&implicant);
  return 0;
}

static int32_t add_local_implicant_cube(model_t *mdl, term_manager_t *mngr,
                                        uint32_t n, const term_t f[],
                                        int_array_hset_t *seen,
                                        ivector_t *cube_stream) {
  bool added;

  return add_normalized_implicant_cube(mdl, mngr, n, f, seen, cube_stream, &added);
}

static int32_t enumerate_implicant_cubes_with_status(model_t *mdl, term_manager_t *mngr,
                                                     uint32_t n, const term_t f[],
                                                     uint32_t max_cubes,
                                                     ivector_t *cube_stream,
                                                     cube_enum_status_t *status) {
  evaluator_t eval;
  abs_builder_t builder;
  smt_core_t core;
  int_array_hset_t seen;
  ivector_t selected_lits, cube;
  bool_node_id_t root;
  smt_status_t core_status;
  int32_t code;
  uint32_t num_cubes;
  bool builder_inited, core_inited, seen_inited, added;

  init_cube_enum_status(status);
  ivector_reset(cube_stream);

  init_evaluator(&eval, mdl);
  init_abs_builder(&builder, mdl, mngr, &eval, max_cubes);
  init_int_array_hset(&seen, 0);
  init_ivector(&selected_lits, 16);
  init_ivector(&cube, 16);
  builder_inited = true;
  seen_inited = true;
  core_inited = false;
  code = 0;
  num_cubes = 0;

  if (n == 0) {
    num_cubes = 1;
    status->sat_exhausted = true;
    goto cleanup;
  }

  if (abstract_formula_array(&builder, n, f, &root) != ABS_OK) {
    status->used_local_fallback = true;
    code = add_local_implicant_cube(mdl, mngr, n, f, &seen, cube_stream);
    if (code == 0) {
      num_cubes = 1;
    }
    status->sat_exhausted = true;
    goto cleanup;
  }

  if (bool_node_is_false(root)) {
    code = MDL_EVAL_FORMULA_FALSE;
    goto cleanup;
  }

  if (bool_node_is_true(root)) {
    num_cubes = 1;
    status->sat_exhausted = true;
    goto cleanup;
  }

  if (! builder.decomposed) {
    status->used_local_fallback = true;
    code = add_local_implicant_cube(mdl, mngr, n, f, &seen, cube_stream);
    if (code == 0) {
      num_cubes = 1;
    }
    status->sat_exhausted = true;
    goto cleanup;
  }

  init_abstraction_core(&builder, root, &core);
  core_inited = true;

  for (;;) {
    if (max_cubes != 0 && num_cubes >= max_cubes) {
      status->budget_exhausted = true;
      break;
    }

    core_status = bool_core_solve_negative(&core);
    if (core_status == YICES_STATUS_UNSAT) {
      status->sat_exhausted = true;
      break;
    }
    if (core_status != YICES_STATUS_SAT) {
      code = GEN_EVAL_INTERNAL_ERROR;
      goto cleanup;
    }

    collect_selected_literals(&builder, &core, &selected_lits, &cube);
#ifndef NDEBUG
    assert_selected_satisfies_root(&builder, root, &selected_lits);
#endif

    code = add_normalized_implicant_cube(mdl, mngr, cube.size, cube.data, &seen, cube_stream, &added);
    if (code != 0) {
      goto cleanup;
    }
    if (added) {
      num_cubes ++;
    } else {
      status->saw_duplicate = true;
    }

    if (selected_lits.size == 0) {
      status->sat_exhausted = true;
      break;
    }

    smt_clear(&core);
    add_superset_blocker_to_core(&core, &selected_lits);
    if (core.inconsistent) {
      status->sat_exhausted = true;
      break;
    }
  }

 cleanup:
  delete_ivector(&cube);
  delete_ivector(&selected_lits);
  if (core_inited) delete_smt_core(&core);
  if (seen_inited) delete_int_array_hset(&seen);
  if (builder_inited) delete_abs_builder(&builder);
  delete_evaluator(&eval);
  return code < 0 ? code : (int32_t) num_cubes;
}

int32_t get_implicant_cubes(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
                            uint32_t max_cubes, ivector_t *cubes) {
  cube_enum_status_t status;

  return enumerate_implicant_cubes_with_status(mdl, mngr, n, f, max_cubes, cubes, &status);
}

static void bool_dag_reset_tseitin(bool_dag_t *dag) {
  uint32_t i;

  for (i = 0; i < dag->size; i++) {
    dag->data[i].tseitin = null_literal;
  }
}

static int32_t append_projected_cube_term(model_t *mdl, term_manager_t *mngr,
                                          arith_construct_preprocess_cache_t *construct_cache,
                                          rdiv_preprocess_cache_t *rdiv_cache,
                                          uint32_t nelims, const term_t elim[],
                                          const term_t *cube_lits, uint32_t cube_size,
                                          int32_t *extra_error,
                                          bool *have_first, bool *multiple,
                                          ivector_t *first_projected, ivector_t *cube_terms) {
  ivector_t projected;
  term_t cube_term;
  int32_t code;

  init_ivector(&projected, 4);
  code = project_one_cube_into(mdl, mngr, construct_cache, rdiv_cache,
                               cube_lits, cube_size, nelims, elim, &projected, extra_error);
  if (code != 0) {
    delete_ivector(&projected);
    return code;
  }

  if (! *have_first) {
    ivector_reset(first_projected);
    ivector_add(first_projected, projected.data, projected.size);
    *have_first = true;
  } else {
    if (! *multiple) {
      cube_term = mk_and_safe(mngr, first_projected->size, first_projected->data);
      if (cube_term == NULL_TERM) {
        delete_ivector(&projected);
        return GEN_EVAL_INTERNAL_ERROR;
      }
      ivector_push(cube_terms, cube_term);
      *multiple = true;
    }
    cube_term = mk_and_safe(mngr, projected.size, projected.data);
    if (cube_term == NULL_TERM) {
      delete_ivector(&projected);
      return GEN_EVAL_INTERNAL_ERROR;
    }
    ivector_push(cube_terms, cube_term);
  }

  delete_ivector(&projected);
  return 0;
}

static int32_t gen_model_by_proj_sat_guided(model_t *mdl, term_manager_t *mngr,
                                            uint32_t nelims, const term_t elim[],
                                            ivector_t *v, uint32_t cube_budget,
                                            int32_t *extra_error) {
  cube_enum_status_t enum_status;
  ivector_t input, input_abs, cubes;
  ivector_t first_projected, cube_terms, local;
  arith_construct_preprocess_cache_t *construct_cache;
  rdiv_preprocess_cache_t *rdiv_cache;
  proj_flag_t pflag;
  uint32_t i, start, num_cubes, cube_index;
  int32_t code;
  bool have_first, multiple;
  term_t collected;
  const term_t *cube_lits;

  init_ivector(&input, v->size);
  ivector_add(&input, v->data, v->size);
  init_ivector(&input_abs, v->size);
  ivector_reset(v);

  code = 0;
  construct_cache = NULL;
  rdiv_cache = NULL;

  init_ivector(&cubes, 16);
  init_ivector(&first_projected, 8);
  init_ivector(&cube_terms, 8);
  init_ivector(&local, 8);
  have_first = false;
  multiple = false;

  pflag = preprocess_abs_terms(mngr, input.size, input.data, &input_abs, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto cleanup;
  }

  construct_cache = new_arith_construct_preprocess_cache(mdl, mngr);
  rdiv_cache = new_rdiv_preprocess_cache(mdl, mngr);

  code = enumerate_implicant_cubes_with_status(mdl, mngr, input_abs.size, input_abs.data,
                                               cube_budget, &cubes, &enum_status);
  if (code < 0) {
    goto cleanup;
  }
  // The enumerator returns the number of encoded cubes on success. A
  // model-true formula always has at least one implicant cube, possibly
  // the empty cube represented by an empty stream.
  assert(code > 0);
  num_cubes = (uint32_t) code;

  start = 0;
  cube_index = 0;
  for (i = 0; i <= cubes.size && cube_index < num_cubes; i++) {
    if (i == cubes.size || cubes.data[i] == NULL_TERM) {
      cube_lits = start < i ? cubes.data + start : NULL;
      code = append_projected_cube_term(mdl, mngr, construct_cache, rdiv_cache,
                                        nelims, elim, cube_lits, i - start,
                                        extra_error, &have_first, &multiple,
                                        &first_projected, &cube_terms);
      if (code != 0) {
        // Projection error on this cube (typically a literal contains a
        // term-kind the projector doesn't support, e.g. in non-MCSAT
        // builds a non-linear arithmetic term -> PROJ_ERROR_NON_LINEAR,
        // or a function application -> PROJ_ERROR_UNSUPPORTED_ARITH_TERM).
        // Drop this cube and try other implicants of F: a different
        // SAT-guided choice may avoid the offending literal entirely.
        code = 0;
      }
      start = i + 1;
      cube_index ++;
    }
  }
  assert(cube_index == num_cubes);

  if (!have_first) {
    // If no cube projected successfully, local will surface the underlying
    // projector error code via its own path.
    ivector_reset(&local);
    ivector_add(&local, input_abs.data, input_abs.size);
    code = gen_model_by_proj_local_with_cache(mdl, mngr, nelims, elim, &local, extra_error,
                                              construct_cache, rdiv_cache);
    if (code != 0) {
      goto cleanup;
    }
    ivector_reset(v);
    ivector_add(v, local.data, local.size);
    goto cleanup;
  }

  // SAT exhausted naturally and at least one cube projected.
  assert(have_first);
  if (! multiple) {
    ivector_add(v, first_projected.data, first_projected.size);
  } else {
    collected = mk_or_safe(mngr, cube_terms.size, cube_terms.data);
    if (collected == NULL_TERM) {
      ivector_reset(&local);
      ivector_add(&local, input_abs.data, input_abs.size);
      code = gen_model_by_proj_local_with_cache(mdl, mngr, nelims, elim, &local, extra_error,
                                                construct_cache, rdiv_cache);
      if (code == 0) {
        ivector_add(v, local.data, local.size);
      }
    } else {
      ivector_push(v, collected);
    }
  }

 cleanup:
  if (rdiv_cache != NULL) delete_rdiv_preprocess_cache(rdiv_cache);
  if (construct_cache != NULL) delete_arith_construct_preprocess_cache(construct_cache);
  delete_ivector(&local);
  delete_ivector(&cube_terms);
  delete_ivector(&first_projected);
  delete_ivector(&cubes);
  delete_ivector(&input_abs);
  delete_ivector(&input);
  return code;
}



/*
 * Generalization by substitution
 * - mdl = model
 * - mngr = relevant term manager
 * - f[0 ... n-1] = formula true in the model
 * - elim[0 ... nelim -1] = variables to eliminate
 * - v = result vector
 *
 * - returned code: 0 if no error, an error code otherwise
 * - error codes are listed in generalization.h
 */
int32_t gen_model_by_substitution(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[], 
				  uint32_t nelims, const term_t elim[], ivector_t *v) {

  ivector_copy(v, f, n);
  assert(v->size == n);
  return gen_model_by_subst(mdl, mngr, nelims, elim, v);
}


/*
 * Generalize by projection (wide variant; opt-in via
 * YICES_GEN_BY_PROJ_WIDE).
 *
 * Walks the Boolean structure of f[], enumerates model-true Boolean
 * implicants via a SAT-guided loop, projects each implicant as a cube
 * through the legacy implicant+project pipeline, and unions the results
 * at the term level. Output is always at least as broad as
 * gen_model_by_projection_local and is often strictly broader when f[]
 * has Boolean structure the model satisfies in more than one way.
 * Recommended for CEGAR-style outer loops over quantifier prefixes.
 *
 * cube_budget caps the number of distinct normalized cubes attempted
 * for projection. cube_budget == 0 means unbounded (the Boolean
 * enumeration is always finite because each iteration adds a blocker
 * clause).
 * On budget exhaustion, if at least one cube projected successfully, the
 * wide result is the union of the collected projected cubes. If no cube
 * projected successfully, the wide path falls back to local projection.
 */
int32_t gen_model_by_projection(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				uint32_t nelims, const term_t elim[], ivector_t *v,
				uint32_t cube_budget, int32_t *extra_error) {
  ivector_copy(v, f, n);
  assert(v->size == n);
  return gen_model_by_proj_sat_guided(mdl, mngr, nelims, elim, v, cube_budget, extra_error);
}


/*
 * Generalize by projection (legacy local pipeline).
 *
 * Builds a single literal implicant of f[] at the model and projects
 * that flat conjunction. The output is sign-invariant for the chosen
 * implicant. Cheaper per call than the wide variant but commits to one
 * disjunct when f[] has Boolean structure.
 */
int32_t gen_model_by_projection_local(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
                                      uint32_t nelims, const term_t elim[], ivector_t *v, int32_t *extra_error) {
  ivector_copy(v, f, n);
  assert(v->size == n);
  return gen_model_by_proj_local(mdl, mngr, nelims, elim, v, extra_error);
}



/*
 * Generalize mdl: two passes:
 * - 1) eliminate the discrete variables by substitution
 * - 2) use the legacy projection (gen_model_by_proj_local) to eliminate
 *      the real variables
 *
 * Callers who want the SAT-guided wide projection for pass 2 should call
 * gen_model_by_projection directly or go through the public API with
 * YICES_GEN_BY_PROJ_WIDE.
 */
int32_t generalize_model(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
			 uint32_t nelims, const term_t elim[], ivector_t *v,
			 int32_t *extra_error) {
  term_table_t *terms;
  ivector_t discretes;
  ivector_t reals;
  int32_t code;

  // if n == 0, there's nothing to do
  code = 0;
  if (n > 0) {
    terms = term_manager_get_terms(mngr);
    init_ivector(&reals, 10);
    init_ivector(&discretes, 10);
    split_elim_array(terms, nelims, elim, &reals, &discretes);
   
    ivector_copy(v, f, n);
    if (discretes.size > 0) {
      code = gen_model_by_subst(mdl, mngr, discretes.size, discretes.data, v);
    }
    if (code == 0 && reals.size > 0) {
      code = gen_model_by_proj_local(mdl, mngr, reals.size, reals.data, v, extra_error);
    }

    delete_ivector(&reals);
    delete_ivector(&discretes);
  }

  return code;
}
