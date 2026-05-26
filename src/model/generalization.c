/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
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
 *   implicant rather than truth-invariant for the formula.
 *
 * - "wide" (gen_model_by_proj_sat_guided): the public default.
 *   Builds a model-pruned Boolean abstraction of f[], enumerates
 *   model-true Boolean implicants with a SAT solver and blocker
 *   clauses, projects each implicant as a cube through the legacy
 *   implicant-then-project pipeline, and unions the results at the
 *   term level.
 *
 *   If SAT-guided enumeration hits the cube budget or a projection
 *   error after collecting some cubes, the result is OR(collected,
 *   local). If no SAT-guided cube has been collected, it returns the
 *   local cell. The older eager Cartesian-product walker
 *   (gen_model_by_proj_wide) is kept as a conservative internal
 *   fallback for Boolean-abstraction failures.
 */

#include <assert.h>

#include "model/generalization.h"
#include "model/model_eval.h"
#include "model/model_queries.h"
#include "model/projection.h"
#include "model/val_to_term.h"
#include "solvers/cdcl/new_sat_solver.h"
#include "terms/term_manager.h"
#include "terms/term_substitution.h"
#include "terms/terms.h"
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
static int32_t gen_model_by_proj_local(model_t *mdl, term_manager_t *mngr, uint32_t nelims, const term_t elim[], ivector_t *v, int32_t *extra_error) {
  ivector_t implicant;
  int32_t code;
  proj_flag_t pflag;

  init_ivector(&implicant, 10);
  code = get_implicant(mdl, mngr, LIT_COLLECTOR_ALL_OPTIONS, v->size, v->data, &implicant);
  if (code < 0) {
    // implicant construction failed
    code = gen_implicant_error(code);
    goto done;
  }
  
  ivector_reset(v); // reset v to collect the projection result
  code = 0;
  pflag = project_literals(mdl, mngr, implicant.size, implicant.data, nelims, elim, v, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
  }

 done:
  delete_ivector(&implicant);

  return code;
  
}



/*
 * WIDE PROJECTION: cube enumeration over the Boolean structure
 *
 * The wide variant decomposes f[] along its top-level Boolean
 * connectives (positive OR_TERM as disjunction, negative OR_TERM as
 * conjunction-of-negations via De Morgan, Boolean-typed ITE_TERM as
 * ite -> (cond AND then) OR (NOT cond AND else)) and produces a set
 * of "cubes". Each cube is a list of leaf-level sub-formulas whose
 * conjunction is true at the model and implies f[]. The legacy
 * implicant-then-project pipeline is then applied to each cube
 * independently and the results are unioned at the term level.
 *
 * In the conjunctive case the walk produces a single cube and the
 * result is identical to gen_model_by_proj_local. The wide effect
 * appears only when the formula has Boolean OR / Boolean ITE nodes
 * with multiple disjuncts true at the model.
 */

// Cap on the number of cubes the walk is allowed to produce. If the
// Cartesian-product blowup would exceed this, the wide pipeline aborts
// and falls back to gen_model_by_proj_local.
#define WIDE_CUBE_BUDGET 1024

/*
 * Cube set: a list of cubes stored as a flat literal pool plus a
 * starts vector of offsets.
 *   num_cubes = starts.size - 1
 *   cube i = lits[starts[i] .. starts[i+1])
 * Initial state: starts = [0], lits = [].
 */
typedef struct cube_set_s {
  ivector_t lits;
  ivector_t starts;
} cube_set_t;

static void init_cube_set(cube_set_t *cs) {
  init_ivector(&cs->lits, 16);
  init_ivector(&cs->starts, 8);
  ivector_push(&cs->starts, 0);
}

static void delete_cube_set(cube_set_t *cs) {
  delete_ivector(&cs->lits);
  delete_ivector(&cs->starts);
}

static inline uint32_t cube_set_num_cubes(const cube_set_t *cs) {
  assert(cs->starts.size >= 1);
  return cs->starts.size - 1;
}

// Append a singleton cube containing the single literal l.
static void cube_set_add_singleton(cube_set_t *cs, term_t l) {
  ivector_push(&cs->lits, l);
  ivector_push(&cs->starts, cs->lits.size);
}

// Append every cube from src to dest (set union of cube lists).
static void cube_set_extend(cube_set_t *dest, const cube_set_t *src) {
  uint32_t i, n;
  uint32_t base;

  n = cube_set_num_cubes(src);
  if (n == 0) return;

  base = dest->lits.size;
  for (i = 0; i < src->lits.size; i++) {
    ivector_push(&dest->lits, src->lits.data[i]);
  }
  // src->starts[0] is always 0; we only need offsets [1 .. n].
  for (i = 1; i <= n; i++) {
    ivector_push(&dest->starts, base + (uint32_t) src->starts.data[i]);
  }
}

// Replace dest with the Cartesian product dest x src (each cube from
// dest concatenated with each cube from src). Returns false if the
// product would exceed the budget; in that case dest is left in an
// unspecified-but-safe state and the caller must abort the walk.
static bool cube_set_product(cube_set_t *dest, const cube_set_t *src, uint32_t budget) {
  uint32_t i, j;
  uint32_t na, nb;
  cube_set_t tmp;

  na = cube_set_num_cubes(dest);
  nb = cube_set_num_cubes(src);

  if (na == 0 || nb == 0) {
    // Empty product is empty.
    ivector_reset(&dest->lits);
    ivector_reset(&dest->starts);
    ivector_push(&dest->starts, 0);
    return true;
  }

  if ((uint64_t) na * (uint64_t) nb > (uint64_t) budget) {
    return false;
  }

  init_cube_set(&tmp);
  for (i = 0; i < na; i++) {
    int32_t a_start = dest->starts.data[i];
    int32_t a_end   = dest->starts.data[i+1];
    for (j = 0; j < nb; j++) {
      int32_t b_start = src->starts.data[j];
      int32_t b_end   = src->starts.data[j+1];
      int32_t k;
      // New cube = dest[i] ++ src[j]
      for (k = a_start; k < a_end; k++) {
        ivector_push(&tmp.lits, dest->lits.data[k]);
      }
      for (k = b_start; k < b_end; k++) {
        ivector_push(&tmp.lits, src->lits.data[k]);
      }
      ivector_push(&tmp.starts, tmp.lits.size);
    }
  }

  // Move tmp into dest.
  ivector_reset(&dest->lits);
  ivector_reset(&dest->starts);
  for (i = 0; i < tmp.lits.size; i++)   ivector_push(&dest->lits,   tmp.lits.data[i]);
  for (i = 0; i < tmp.starts.size; i++) ivector_push(&dest->starts, tmp.starts.data[i]);
  delete_cube_set(&tmp);
  return true;
}


/*
 * Walk-status flags.
 *   WIDE_OK        : cubes successfully appended to out.
 *   WIDE_BUDGET    : cube budget exceeded; caller should fall back to local.
 *   WIDE_FALSE_AT  : some sub-term that was supposed to be true at the model
 *                    is actually false (formula not true at model).
 *   WIDE_INTERNAL  : unexpected internal failure.
 */
typedef enum {
  WIDE_OK = 0,
  WIDE_BUDGET = 1,
  WIDE_FALSE_AT = 2,
  WIDE_INTERNAL = 3,
} wide_status_t;


/*
 * Recursive walker. Appends cubes for the formula t (interpreted with
 * polarity bit) into `out`. The model must satisfy t; this is checked
 * at OR/ITE nodes (we descend only on satisfied disjuncts).
 *
 * The walker decomposes:
 *   - OR_TERM positive : pick all satisfied disjuncts, union their cube sets;
 *   - OR_TERM negative : conjunction-of-negations via De Morgan,
 *                        Cartesian-product the cube sets of each negated arg;
 *   - ITE_TERM (Boolean type) : decompose to (cond AND branch_taken).
 *   - Everything else: emit a singleton cube containing the literal
 *     (with polarity preserved).
 */
static wide_status_t wide_collect_cubes(term_t t, term_table_t *terms,
                                        evaluator_t *eval, cube_set_t *out) {
  term_kind_t kind;
  term_t base;
  bool neg;
  composite_term_t *desc;
  cube_set_t child;
  uint32_t i, n;
  wide_status_t st;

  base = unsigned_term(t);
  neg  = is_neg_term(t);
  kind = term_kind(terms, base);

  // Handle Boolean structural nodes. Anything else is treated as a
  // leaf literal.
  if (kind == OR_TERM) {
    desc = or_term_desc(terms, base);
    n = desc->arity;

    if (!neg) {
      // Positive OR: walk each disjunct that holds at the model and
      // append all their cubes to out.
      bool any = false;
      for (i = 0; i < n; i++) {
        term_t arg = desc->arg[i];
        if (eval_to_true_in_model(eval, arg)) {
          any = true;
          init_cube_set(&child);
          st = wide_collect_cubes(arg, terms, eval, &child);
          if (st == WIDE_OK) {
            cube_set_extend(out, &child);
          }
          delete_cube_set(&child);
          if (st != WIDE_OK) return st;
          if (cube_set_num_cubes(out) > WIDE_CUBE_BUDGET) return WIDE_BUDGET;
        }
      }
      if (!any) {
        // Disjunction is true at model but no disjunct evaluates true:
        // model not consistent. Treat as caller-side error.
        return WIDE_FALSE_AT;
      }
      return WIDE_OK;
    } else {
      // Negative OR = AND of negations. Each negated arg must be true
      // at the model; we Cartesian-product their cube sets into one
      // accumulator.
      cube_set_t accum;
      init_cube_set(&accum);
      // Start with a single empty cube.
      ivector_push(&accum.starts, 0);  // accum.starts now = [0, 0], so 1 empty cube.
      // wait: initially starts = [0]. We need [0, 0] to encode one empty cube.
      // (init_cube_set already pushed 0 once. We push one more to mark the end of the
      // empty cube.)

      for (i = 0; i < n; i++) {
        term_t neg_arg = opposite_term(desc->arg[i]);
        if (!eval_to_true_in_model(eval, neg_arg)) {
          // Should be true (since the AND-of-negations is true at model)
          delete_cube_set(&accum);
          return WIDE_FALSE_AT;
        }
        init_cube_set(&child);
        st = wide_collect_cubes(neg_arg, terms, eval, &child);
        if (st != WIDE_OK) {
          delete_cube_set(&child);
          delete_cube_set(&accum);
          return st;
        }
        bool ok = cube_set_product(&accum, &child, WIDE_CUBE_BUDGET);
        delete_cube_set(&child);
        if (!ok) {
          delete_cube_set(&accum);
          return WIDE_BUDGET;
        }
      }

      cube_set_extend(out, &accum);
      delete_cube_set(&accum);
      return WIDE_OK;
    }
  }

  if (kind == ITE_TERM || kind == ITE_SPECIAL) {
    // Boolean-typed ITE only: (ite c a b) where a and b are Boolean.
    // For non-Boolean ITE, fall through to leaf treatment - the
    // implicant builder will handle it.
    if (is_boolean_term(terms, base)) {
      composite_term_t *idesc = ite_term_desc(terms, base);
      term_t cond   = idesc->arg[0];
      term_t then_b = idesc->arg[1];
      term_t else_b = idesc->arg[2];
      term_t branch_cond, branch;

      if (eval_to_true_in_model(eval, cond)) {
        branch_cond = cond;
        branch      = neg ? opposite_term(then_b) : then_b;
      } else {
        branch_cond = opposite_term(cond);
        branch      = neg ? opposite_term(else_b) : else_b;
      }

      // Cubes for (branch_cond AND branch) = product.
      cube_set_t cs_cond, cs_branch;
      init_cube_set(&cs_cond);
      init_cube_set(&cs_branch);

      st = wide_collect_cubes(branch_cond, terms, eval, &cs_cond);
      if (st == WIDE_OK) st = wide_collect_cubes(branch, terms, eval, &cs_branch);

      if (st == WIDE_OK) {
        bool ok = cube_set_product(&cs_cond, &cs_branch, WIDE_CUBE_BUDGET);
        if (ok) {
          cube_set_extend(out, &cs_cond);
        } else {
          st = WIDE_BUDGET;
        }
      }
      delete_cube_set(&cs_cond);
      delete_cube_set(&cs_branch);
      return st;
    }
    // else fall through: non-Boolean ITE is part of an arith/leaf term.
  }

  // Leaf: emit a singleton cube containing the literal (with polarity).
  cube_set_add_singleton(out, t);
  return WIDE_OK;
}


/*
 * Project a single cube via the legacy implicant+project pipeline.
 * The cube's literals are normalized through get_implicant (which
 * expands ITE-inside-arith, etc.) and then projected.
 *
 * The projected literals are appended to *out (a list of literals
 * whose AND is the projected cube). out is not reset.
 */
static int32_t project_one_cube_into(model_t *mdl, term_manager_t *mngr,
                                     const term_t *cube_lits, uint32_t cube_size,
                                     uint32_t nelims, const term_t elim[],
                                     ivector_t *out, int32_t *extra_error) {
  ivector_t implicant;
  proj_flag_t pflag;
  int32_t code;

  init_ivector(&implicant, cube_size);

  code = get_implicant(mdl, mngr, LIT_COLLECTOR_ALL_OPTIONS, cube_size, cube_lits, &implicant);
  if (code < 0) {
    code = gen_implicant_error(code);
    goto cleanup;
  }

  pflag = project_literals(mdl, mngr, implicant.size, implicant.data,
                           nelims, elim, out, extra_error);
  if (pflag != PROJ_NO_ERROR) {
    code = gen_projection_error(pflag);
    goto cleanup;
  }

  code = 0;

 cleanup:
  delete_ivector(&implicant);
  return code;
}


/*
 * Wide-projection core procedure.
 *
 * Treats the input formulas in v as a single conjunction
 *   F(X, y) = f[0] AND f[1] AND ... AND f[n-1]
 * and produces a generalization G(X) such that G(X) is true at mdl
 * and G(X) implies (EXISTS y. F(X, y)).
 *
 * Algorithm:
 *   1. Walk each f[i] to obtain a cube set C_i (the cubes true at
 *      mdl whose conjunction implies f[i]).
 *   2. Form the joint cube set C = C_0 x C_1 x ... x C_{n-1}
 *      (Cartesian product). Each joint cube is a list of literals
 *      whose conjunction is true at mdl and implies F.
 *   3. Project each joint cube through the legacy implicant+project
 *      pipeline, producing an arithmetic-cube term G_k.
 *   4. Result is the disjunction OR_k G_k, pushed as a single
 *      element of v.
 *
 * The Cartesian-product step is essential: f[i] and f[j] can share
 * the eliminated variables, so per-i projection followed by AND
 * would over-approximate (existential does not distribute over AND
 * across different witnesses).
 *
 * On budget exhaustion or unsupported constructs the wide pipeline
 * falls back transparently to gen_model_by_proj_local.
 *
 * Pre: v contains the input formulas (caller copies f[] into v before
 * calling this, mirroring gen_model_by_proj_local's contract).
 */
static int32_t gen_model_by_proj_wide(model_t *mdl, term_manager_t *mngr,
                                      uint32_t nelims, const term_t elim[],
                                      ivector_t *v, int32_t *extra_error) {
  term_table_t *terms;
  evaluator_t eval;
  cube_set_t joint, child;
  ivector_t cube_terms;
  ivector_t input;
  uint32_t fi, ci, n_cubes;
  int32_t code;
  wide_status_t st;
  bool needs_fallback;
  bool joint_inited;

  terms = term_manager_get_terms(mngr);
  init_evaluator(&eval, mdl);

  // Copy the original input out of v; we'll overwrite v with results.
  init_ivector(&input, v->size);
  ivector_add(&input, v->data, v->size);
  ivector_reset(v);

  init_ivector(&cube_terms, 16);
  needs_fallback = false;
  joint_inited = false;
  code = 0;

  if (input.size == 0) {
    // Nothing to project.
    goto cleanup;
  }

  // Initialize joint with a single empty cube so the first product
  // step yields exactly the first formula's cubes.
  init_cube_set(&joint);
  ivector_push(&joint.starts, 0);  // starts = [0, 0] -> one empty cube
  joint_inited = true;

  for (fi = 0; fi < input.size; fi++) {
    term_t f_i = input.data[fi];
    bool ok;

    init_cube_set(&child);
    st = wide_collect_cubes(f_i, terms, &eval, &child);

    if (st == WIDE_BUDGET || st == WIDE_INTERNAL) {
      delete_cube_set(&child);
      needs_fallback = true;
      break;
    }
    if (st == WIDE_FALSE_AT) {
      delete_cube_set(&child);
      code = MDL_EVAL_FORMULA_FALSE;
      goto cleanup;
    }

    n_cubes = cube_set_num_cubes(&child);
    if (n_cubes == 0) {
      delete_cube_set(&child);
      code = MDL_EVAL_FORMULA_FALSE;
      goto cleanup;
    }

    ok = cube_set_product(&joint, &child, WIDE_CUBE_BUDGET);
    delete_cube_set(&child);
    if (!ok) {
      needs_fallback = true;
      break;
    }
  }

  if (!needs_fallback) {
    n_cubes = cube_set_num_cubes(&joint);
    if (n_cubes == 0) {
      // All input formulas are vacuously true (empty conjunction):
      // the generalization is true_term.
      ivector_push(v, true_term);
      goto cleanup;
    }

    if (n_cubes == 1) {
      // Single cube: emit the projected literals directly into v
      // (matches the legacy flat-literal output shape exactly).
      int32_t start = joint.starts.data[0];
      int32_t end   = joint.starts.data[1];
      code = project_one_cube_into(mdl, mngr,
                                   joint.lits.data + start, (uint32_t)(end - start),
                                   nelims, elim, v, extra_error);
      goto cleanup;
    }

    // Multiple cubes: project each into its own AND-term, then OR them.
    ivector_reset(&cube_terms);
    for (ci = 0; ci < n_cubes; ci++) {
      int32_t start = joint.starts.data[ci];
      int32_t end   = joint.starts.data[ci+1];
      ivector_t projected;
      term_t cube_term;

      init_ivector(&projected, 4);
      code = project_one_cube_into(mdl, mngr,
                                   joint.lits.data + start, (uint32_t)(end - start),
                                   nelims, elim, &projected, extra_error);
      if (code != 0) {
        delete_ivector(&projected);
        goto cleanup;
      }
      cube_term = mk_and_safe(mngr, projected.size, projected.data);
      delete_ivector(&projected);
      if (cube_term == NULL_TERM) {
        needs_fallback = true;
        break;
      }
      ivector_push(&cube_terms, cube_term);
    }

    if (!needs_fallback) {
      // OR the projected cubes into a single result term.
      term_t result = mk_or_safe(mngr, cube_terms.size, cube_terms.data);
      if (result == NULL_TERM) {
        needs_fallback = true;
      } else {
        ivector_push(v, result);
      }
    }
  }

 cleanup:
  if (joint_inited) delete_cube_set(&joint);
  delete_ivector(&cube_terms);

  if (needs_fallback) {
    // Restore v with the original input and run the legacy pipeline.
    ivector_reset(v);
    ivector_add(v, input.data, input.size);
    code = gen_model_by_proj_local(mdl, mngr, nelims, elim, v, extra_error);
  }

  delete_ivector(&input);
  delete_evaluator(&eval);
  return code;
}


/*
 * SAT-GUIDED WIDE PROJECTION
 *
 * This front end replaces eager Cartesian-product cube construction by
 * model-pruned Boolean abstraction plus SAT-guided implicant enumeration.
 * Each emitted Boolean implicant is mapped back to a theory cube and
 * projected by project_one_cube_into above.
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
  int_hmap_t atom_to_bvar;
  ivector_t bvar_to_atom;
  int_hmap_t cache_signed;
  bool_dag_t dag;
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

static void init_abs_builder(abs_builder_t *b, model_t *mdl, term_manager_t *mngr, evaluator_t *eval) {
  b->mngr = mngr;
  b->terms = term_manager_get_terms(mngr);
  b->eval = eval;
  init_int_hmap(&b->atom_to_bvar, 0);
  init_ivector(&b->bvar_to_atom, 16);
  ivector_push(&b->bvar_to_atom, NULL_TERM); // var 0 is reserved by new_sat_solver
  init_int_hmap(&b->cache_signed, 0);
  init_bool_dag(&b->dag);
  b->decomposed = false;
  (void) mdl;
}

static void delete_abs_builder(abs_builder_t *b) {
  // After ABS_ERROR, discard the whole builder: rollback does not undo caches.
  delete_bool_dag(&b->dag);
  delete_int_hmap(&b->cache_signed);
  delete_ivector(&b->bvar_to_atom);
  delete_int_hmap(&b->atom_to_bvar);
}

static bvar_t abs_builder_get_atom_var(abs_builder_t *b, term_t atom) {
  int_hmap_pair_t *r;
  bvar_t v;

  assert(atom == unsigned_term(atom));
  r = int_hmap_get(&b->atom_to_bvar, atom);
  if (r->val < 0) {
    v = (bvar_t) b->bvar_to_atom.size;
    r->val = v;
    ivector_push(&b->bvar_to_atom, atom);
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

static abs_status_t abstract_boolean_ite(abs_builder_t *b, term_t base, bool neg, bool_node_id_t *out) {
  composite_term_t *idesc;
  term_t cond, then_b, else_b;
  bool_node_id_t left, right;
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

  init_ivector(&child, 2);
  ivector_push(&child, left);
  ivector_push(&child, right);
  st = bool_dag_mk_or(b, &child, out);
  delete_ivector(&child);
  return st;
}

static abs_status_t abstract_leaf(abs_builder_t *b, term_t t, bool_node_id_t *out) {
  term_t atom;
  bvar_t v;
  literal_t lit;

  atom = unsigned_term(t);
  v = abs_builder_get_atom_var(b, atom);
  lit = is_neg_term(t) ? neg_lit(v) : pos_lit(v);
  *out = bool_dag_add_lit(&b->dag, lit);
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

    if ((kind == ITE_TERM || kind == ITE_SPECIAL) && is_boolean_term(b->terms, base)) {
      b->decomposed = true;
      st = abstract_boolean_ite(b, base, neg, out);
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

static void sat_add_clause(sat_solver_t *sat, uint32_t n, literal_t *lit) {
  nsat_solver_simplify_and_add_clause(sat, n, lit);
}

static void sat_add_unit_clause(sat_solver_t *sat, literal_t l) {
  literal_t clause[1];

  clause[0] = l;
  sat_add_clause(sat, 1, clause);
}

static void sat_add_binary_clause(sat_solver_t *sat, literal_t l1, literal_t l2) {
  literal_t clause[2];

  clause[0] = l1;
  clause[1] = l2;
  sat_add_clause(sat, 2, clause);
}

static literal_t clausify_node(bool_dag_t *dag, sat_solver_t *sat, bool_node_id_t id) {
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
    result = pos_lit(nsat_solver_new_var(sat));
    init_ivector(&clause, node->count + 1);
    ivector_push(&clause, result);
    for (i = 0; i < node->count; i++) {
      child_lit = clausify_node(dag, sat, dag->children.data[node->start + i]);
      sat_add_binary_clause(sat, not(result), child_lit);
      ivector_push(&clause, not(child_lit));
    }
    sat_add_clause(sat, clause.size, clause.data);
    delete_ivector(&clause);
    break;

  case BOOL_NODE_OR:
    result = pos_lit(nsat_solver_new_var(sat));
    init_ivector(&clause, node->count + 1);
    ivector_push(&clause, not(result));
    for (i = 0; i < node->count; i++) {
      child_lit = clausify_node(dag, sat, dag->children.data[node->start + i]);
      sat_add_binary_clause(sat, not(child_lit), result);
      ivector_push(&clause, child_lit);
    }
    sat_add_clause(sat, clause.size, clause.data);
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

static void bool_dag_reset_tseitin(bool_dag_t *dag) {
  uint32_t i;

  for (i = 0; i < dag->size; i++) {
    dag->data[i].tseitin = null_literal;
  }
}

static bool sat_literal_true(sat_solver_t *sat, literal_t lit) {
  return lit_is_true(sat, lit);
}

static bool sat_node_true(bool_dag_t *dag, sat_solver_t *sat, bool_node_id_t id) {
  bool_node_t *node;
  uint32_t i;

  node = &dag->data[id];
  switch (node->kind) {
  case BOOL_NODE_TRUE:
    return true;
  case BOOL_NODE_FALSE:
    return false;
  case BOOL_NODE_LIT:
    return sat_literal_true(sat, node->lit);
  case BOOL_NODE_AND:
    for (i = 0; i < node->count; i++) {
      if (! sat_node_true(dag, sat, dag->children.data[node->start + i])) {
        return false;
      }
    }
    return true;
  case BOOL_NODE_OR:
    for (i = 0; i < node->count; i++) {
      if (sat_node_true(dag, sat, dag->children.data[node->start + i])) {
        return true;
      }
    }
    return false;
  default:
    assert(false);
    return false;
  }
}

static void extract_implicant(bool_dag_t *dag, sat_solver_t *sat, bool_node_id_t id, ivector_t *implicant) {
  bool_node_t *node;
  uint32_t i;
  bool_node_id_t child;

  node = &dag->data[id];
  switch (node->kind) {
  case BOOL_NODE_TRUE:
    break;
  case BOOL_NODE_LIT:
    assert(sat_literal_true(sat, node->lit));
    ivector_push_unique(implicant, node->lit);
    break;
  case BOOL_NODE_AND:
    for (i = 0; i < node->count; i++) {
      extract_implicant(dag, sat, dag->children.data[node->start + i], implicant);
    }
    break;
  case BOOL_NODE_OR:
    for (i = 0; i < node->count; i++) {
      child = dag->children.data[node->start + i];
      if (sat_node_true(dag, sat, child)) {
        extract_implicant(dag, sat, child, implicant);
        break;
      }
    }
    break;
  default:
    assert(false);
    break;
  }
}

static void implicant_to_cube(abs_builder_t *b, const ivector_t *implicant, ivector_t *cube) {
  uint32_t i, n;
  literal_t lit;
  term_t atom;

  ivector_reset(cube);
  n = implicant->size;
  for (i = 0; i < n; i++) {
    lit = implicant->data[i];
    assert(var_of(lit) > const_bvar);
    atom = b->bvar_to_atom.data[var_of(lit)];
    ivector_push(cube, is_pos(lit) ? atom : opposite_term(atom));
  }
}

static void add_blocker_clause_to_sat(sat_solver_t *sat, const ivector_t *implicant) {
  ivector_t clause;
  uint32_t i, n;

  init_ivector(&clause, implicant->size);
  n = implicant->size;
  for (i = 0; i < n; i++) {
    ivector_push(&clause, not(implicant->data[i]));
  }
  sat_add_clause(sat, clause.size, clause.data);
  delete_ivector(&clause);
}

static term_t make_projected_cubes_term(term_manager_t *mngr, bool multiple,
                                        const ivector_t *first_projected, const ivector_t *cube_terms) {
  if (! multiple) {
    return mk_and_safe(mngr, first_projected->size, first_projected->data);
  }
  return mk_or_safe(mngr, cube_terms->size, cube_terms->data);
}

static int32_t append_projected_cube_term(model_t *mdl, term_manager_t *mngr,
                                          uint32_t nelims, const term_t elim[],
                                          ivector_t *cube, int32_t *extra_error,
                                          bool *have_first, bool *multiple,
                                          ivector_t *first_projected, ivector_t *cube_terms) {
  ivector_t projected;
  term_t cube_term;
  int32_t code;

  init_ivector(&projected, 4);
  code = project_one_cube_into(mdl, mngr, cube->data, cube->size, nelims, elim, &projected, extra_error);
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
  evaluator_t eval;
  abs_builder_t builder;
  sat_solver_t sat;
  ivector_t input, implicant, cube;
  ivector_t first_projected, cube_terms, local;
  bool_node_id_t root;
  literal_t root_lit;
  solver_status_t sat_status;
  uint32_t num_cubes;
  int32_t code;
  bool builder_inited;
  bool sat_inited;
  bool have_first, multiple;
  bool needs_fallback, exhausted_sat;
  term_t collected, local_term, result_terms[2];

  init_ivector(&input, v->size);
  ivector_add(&input, v->data, v->size);
  ivector_reset(v);

  init_evaluator(&eval, mdl);
  init_abs_builder(&builder, mdl, mngr, &eval);
  builder_inited = true;
  sat_inited = false;
  code = 0;

  init_ivector(&implicant, 16);
  init_ivector(&cube, 16);
  init_ivector(&first_projected, 8);
  init_ivector(&cube_terms, 8);
  init_ivector(&local, 8);
  have_first = false;
  multiple = false;
  needs_fallback = false;
  exhausted_sat = false;

  if (input.size == 0) {
    ivector_push(v, true_term);
    goto cleanup;
  }

  if (abstract_formula_array(&builder, input.size, input.data, &root) != ABS_OK) {
    // Conservative fallback to the previous wide implementation if the
    // Boolean abstraction can't classify a subterm.
    ivector_reset(v);
    ivector_add(v, input.data, input.size);
    code = gen_model_by_proj_wide(mdl, mngr, nelims, elim, v, extra_error);
    goto cleanup;
  }

  if (bool_node_is_false(root)) {
    code = MDL_EVAL_FORMULA_FALSE;
    goto cleanup;
  }

  if (bool_node_is_true(root)) {
    ivector_push(v, true_term);
    goto cleanup;
  }

  if (! builder.decomposed) {
    ivector_reset(v);
    ivector_add(v, input.data, input.size);
    code = gen_model_by_proj_local(mdl, mngr, nelims, elim, v, extra_error);
    goto cleanup;
  }

  num_cubes = 0;
  init_nsat_solver(&sat, builder.bvar_to_atom.size + builder.dag.size + 8, false);
  sat_inited = true;
  nsat_solver_add_vars(&sat, builder.bvar_to_atom.size - 1);
  bool_dag_reset_tseitin(&builder.dag);
  root_lit = clausify_node(&builder.dag, &sat, root);
  sat_add_unit_clause(&sat, root_lit);
  while (num_cubes < cube_budget) {
    sat_status = nsat_solve(&sat);
    if (sat_status == STAT_UNSAT) {
      exhausted_sat = true;
      break;
    }
    if (sat_status != STAT_SAT) {
      needs_fallback = true;
      break;
    }

    ivector_reset(&implicant);
    extract_implicant(&builder.dag, &sat, root, &implicant);

    implicant_to_cube(&builder, &implicant, &cube);
    code = append_projected_cube_term(mdl, mngr, nelims, elim, &cube, extra_error,
                                      &have_first, &multiple, &first_projected, &cube_terms);
    if (code != 0) {
      needs_fallback = true;
      code = 0;
      break;
    }

    num_cubes ++;
    if (implicant.size == 0) {
      exhausted_sat = true;
      break;
    }
    // Must backtrack away from the SAT model before adding the blocker:
    // otherwise y2sat simplifies all blocker literals to false and creates
    // a spurious empty clause.
    nsat_solver_prepare_for_next_search(&sat);
    add_blocker_clause_to_sat(&sat, &implicant);
  }

  if (! exhausted_sat) {
    needs_fallback = true;
  }

  if (needs_fallback) {
    ivector_reset(&local);
    ivector_add(&local, input.data, input.size);
    code = gen_model_by_proj_local(mdl, mngr, nelims, elim, &local, extra_error);
    if (code != 0) {
      goto cleanup;
    }
    if (! have_first) {
      ivector_reset(v);
      ivector_add(v, local.data, local.size);
    } else {
      collected = make_projected_cubes_term(mngr, multiple, &first_projected, &cube_terms);
      local_term = mk_and_safe(mngr, local.size, local.data);
      ivector_reset(v);
      if (collected == NULL_TERM || local_term == NULL_TERM) {
        ivector_add(v, local.data, local.size);
      } else {
        result_terms[0] = collected;
        result_terms[1] = local_term;
        collected = mk_or_safe(mngr, 2, result_terms);
        if (collected == NULL_TERM) {
          ivector_add(v, local.data, local.size);
        } else {
          ivector_push(v, collected);
        }
      }
    }
    goto cleanup;
  }

  if (! have_first) {
    ivector_push(v, true_term);
  } else if (! multiple) {
    ivector_add(v, first_projected.data, first_projected.size);
  } else {
    collected = mk_or_safe(mngr, cube_terms.size, cube_terms.data);
    if (collected == NULL_TERM) {
      ivector_reset(&local);
      ivector_add(&local, input.data, input.size);
      code = gen_model_by_proj_local(mdl, mngr, nelims, elim, &local, extra_error);
      if (code == 0) {
        ivector_add(v, local.data, local.size);
      }
    } else {
      ivector_push(v, collected);
    }
  }

 cleanup:
  delete_ivector(&local);
  delete_ivector(&cube_terms);
  delete_ivector(&first_projected);
  delete_ivector(&cube);
  delete_ivector(&implicant);
  if (sat_inited) delete_nsat_solver(&sat);
  if (builder_inited) delete_abs_builder(&builder);
  delete_evaluator(&eval);
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
 * Generalize by projection (wide variant, the public default).
 *
 * Walks the Boolean structure of f[], builds a truth-invariant cell
 * via per-cube projection, and unions the results at the term level.
 * Wider output than gen_model_by_projection_local; recommended for
 * CEGAR-style outer loops over quantifier prefixes.
 */
int32_t gen_model_by_projection(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
				uint32_t nelims, const term_t elim[], ivector_t *v, int32_t *extra_error) {
  ivector_copy(v, f, n);
  assert(v->size == n);
  return gen_model_by_proj_sat_guided(mdl, mngr, nelims, elim, v, WIDE_CUBE_BUDGET, extra_error);
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
 * - 2) use projection (wide variant) to eliminate the real variables
 */
int32_t generalize_model(model_t *mdl, term_manager_t *mngr, uint32_t n, const term_t f[],
			 uint32_t nelims, const term_t elim[], ivector_t *v, int32_t *extra_error) {
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
      code = gen_model_by_proj_sat_guided(mdl, mngr, reals.size, reals.data, v, WIDE_CUBE_BUDGET, extra_error);
    }

    delete_ivector(&reals);
    delete_ivector(&discretes);
  }

  return code;
}
