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

#include <assert.h>
#include "context/context.h"
#include "model/models.h"
#include "solvers/egraph/composites.h"
#include "solvers/egraph/egraph.h"
#include "solvers/mcsat_satellite.h"
#include "terms/term_explorer.h"
#include "terms/term_manager.h"
#include "terms/term_substitution.h"
#include "utils/int_hash_sets.h"
#include "utils/memalloc.h"
#include "utils/pair_hash_map2.h"


typedef struct mcsat_atom_object_s {
  uint32_t id;
} mcsat_atom_object_t;

typedef struct mcsat_atom_entry_s {
  term_t atom;
  literal_t lit;
  term_t pos_label;
  term_t neg_label;
  mcsat_atom_object_t *obj;
  bool active;
} mcsat_atom_entry_t;

typedef struct mcsat_eq_entry_s {
  term_t label;
  literal_t source_lit;
} mcsat_eq_entry_t;

struct mcsat_satellite_s {
  context_t *ctx;
  smt_core_t *core;
  egraph_t *egraph;

  context_t mctx;
  term_manager_t tm;

  param_t params;
  bool check_in_propagate;

  int32_t internal_error;

  bool cache_valid;
  uint64_t cache_signature;

  mcsat_atom_entry_t *atoms;
  uint32_t num_atoms;
  uint32_t atom_size;
  uint32_t push_depth;
  ivector_t atom_push_mark;

  int_hmap_t arith_var_to_term;

  mcsat_eq_entry_t *eq;
  uint32_t num_eq;
  uint32_t eq_size;
  uint32_t dlevel;
  pmap2_t eq_active;
  ivector_t eq_level_mark;

  ivector_t assumptions;
  ivector_t assumption_lits;
  int_hmap_t label_to_lit;
  ivector_t conflict;
};


/*
 * Atom/generic vector growth.
 */
static void mcsat_satellite_extend_atoms(mcsat_satellite_t *sat) {
  uint32_t n;
  assert(sat->num_atoms == sat->atom_size);
  n = sat->atom_size + 1;
  n += n >> 1;
  sat->atoms = (mcsat_atom_entry_t *) safe_realloc(sat->atoms, n * sizeof(mcsat_atom_entry_t));
  sat->atom_size = n;
}

static void mcsat_satellite_extend_eq(mcsat_satellite_t *sat) {
  uint32_t n;
  assert(sat->num_eq == sat->eq_size);
  n = sat->eq_size + 1;
  n += n >> 1;
  sat->eq = (mcsat_eq_entry_t *) safe_realloc(sat->eq, n * sizeof(mcsat_eq_entry_t));
  sat->eq_size = n;
}

/*
 * Hash helper for assignment signatures.
 */
static inline uint64_t sig_mix(uint64_t h, uint32_t x) {
  h ^= x;
  h *= UINT64_C(1099511628211);
  return h;
}

static uint64_t mcsat_satellite_signature(const mcsat_satellite_t *sat) {
  uint64_t h;
  uint32_t i, n;

  h = UINT64_C(1469598103934665603);
  n = sat->assumptions.size;
  for (i = 0; i < n; i++) {
    h = sig_mix(h, (uint32_t) sat->assumptions.data[i]);
  }
  return sig_mix(h, n);
}

/*
 * Ensure mctx is ready for assertion.
 */
static void mcsat_satellite_prepare_assertion_state(mcsat_satellite_t *sat) {
  smt_status_t status;
  status = mcsat_status(sat->mctx.mcsat);
  if (status != YICES_STATUS_IDLE) {
    mcsat_clear(sat->mctx.mcsat);
  }
}

/*
 * Assert a formula in the internal MCSAT context.
 */
static int32_t mcsat_satellite_assert_formula(mcsat_satellite_t *sat, term_t f) {
  int32_t code;

  mcsat_satellite_prepare_assertion_state(sat);
  code = mcsat_assert_formulas(sat->mctx.mcsat, 1, &f);
  if (code < 0) {
    sat->internal_error = code;
  }
  return code;
}

/*
 * Track one assumption.
 */
static inline void mcsat_satellite_add_assumption(mcsat_satellite_t *sat, term_t label, literal_t lit) {
  int_hmap_pair_t *p;

  ivector_push(&sat->assumptions, label);
  ivector_push(&sat->assumption_lits, lit);
  if (lit != null_literal) {
    p = int_hmap_get(&sat->label_to_lit, label);
    p->val = lit;
  }
}

/*
 * Build assumption lists from current assignment + active eq/diseq labels.
 */
static void mcsat_satellite_build_assumptions(mcsat_satellite_t *sat, bool complete_with_phase) {
  bval_t v;
  uint32_t i;

  ivector_reset(&sat->assumptions);
  ivector_reset(&sat->assumption_lits);
  int_hmap_reset(&sat->label_to_lit);

  for (i = 0; i < sat->num_atoms; i++) {
    if (!sat->atoms[i].active) {
      continue;
    }

    v = literal_value(sat->core, sat->atoms[i].lit);
    if (v == VAL_TRUE || (complete_with_phase && v == VAL_UNDEF_TRUE)) {
      mcsat_satellite_add_assumption(sat, sat->atoms[i].pos_label, sat->atoms[i].lit);
    } else if (v == VAL_FALSE || (complete_with_phase && v == VAL_UNDEF_FALSE)) {
      mcsat_satellite_add_assumption(sat, sat->atoms[i].neg_label, not(sat->atoms[i].lit));
    }
  }

  for (i = 0; i < sat->num_eq; i++) {
    mcsat_satellite_add_assumption(sat, sat->eq[i].label, sat->eq[i].source_lit);
  }

}

/*
 * Explore a term and collect all Boolean atoms in atoms.
 */
static void collect_boolean_atoms(mcsat_satellite_t *sat, term_t t, int_hset_t *atoms, int_hset_t *visited) {
  term_table_t *terms;
  uint32_t i, nchildren;

  if (t < 0) {
    t = not(t);
  }
  if (int_hset_member(visited, t)) {
    return;
  }
  int_hset_add(visited, t);

  terms = sat->mctx.terms;
  if (term_type(terms, t) == bool_type(terms->types)) {
    int_hset_add(atoms, t);
  }

  if (term_is_projection(terms, t)) {
    collect_boolean_atoms(sat, proj_term_arg(terms, t), atoms, visited);

  } else if (term_is_sum(terms, t)) {
    nchildren = term_num_children(terms, t);
    for (i=0; i<nchildren; i++) {
      term_t child;
      mpq_t q;
      mpq_init(q);
      sum_term_component(terms, t, i, q, &child);
      collect_boolean_atoms(sat, child, atoms, visited);
      mpq_clear(q);
    }

  } else if (term_is_bvsum(terms, t)) {
    int32_t *aux;
    uint32_t nbits;
    term_t child;
    nbits = term_bitsize(terms, t);
    aux = (int32_t *) safe_malloc(nbits * sizeof(int32_t));
    nchildren = term_num_children(terms, t);
    for (i=0; i<nchildren; i++) {
      bvsum_term_component(terms, t, i, aux, &child);
      collect_boolean_atoms(sat, child, atoms, visited);
    }
    safe_free(aux);

  } else if (term_is_product(terms, t)) {
    term_t child;
    uint32_t exp;
    nchildren = term_num_children(terms, t);
    for (i=0; i<nchildren; i++) {
      product_term_component(terms, t, i, &child, &exp);
      collect_boolean_atoms(sat, child, atoms, visited);
    }

  } else if (term_is_composite(terms, t)) {
    nchildren = term_num_children(terms, t);
    for (i=0; i<nchildren; i++) {
      collect_boolean_atoms(sat, term_child(terms, t, i), atoms, visited);
    }
  }
}

/*
 * Build a conflict clause from mcsat interpolant labels.
 * Fallback: use all current tracked assumptions.
 */
static void mcsat_satellite_record_conflict(mcsat_satellite_t *sat) {
  term_t interpolant;
  int_hset_t labels;
  int_hset_t visited;
  int_hset_t seen_lits;
  int_hmap_pair_t *p;
  literal_t l;
  uint32_t i;

  ivector_reset(&sat->conflict);
  init_int_hset(&labels, 0);
  init_int_hset(&visited, 0);
  init_int_hset(&seen_lits, 0);

  interpolant = mcsat_get_unsat_model_interpolant(sat->mctx.mcsat);
  if (interpolant != NULL_TERM) {
    collect_boolean_atoms(sat, interpolant, &labels, &visited);
    p = int_hmap_first_record(&sat->label_to_lit);
    while (p != NULL) {
      if (int_hset_member(&labels, p->key) && p->val != null_literal &&
          !int_hset_member(&seen_lits, p->val)) {
        int_hset_add(&seen_lits, p->val);
        ivector_push(&sat->conflict, not(p->val));
      }
      p = int_hmap_next_record(&sat->label_to_lit, p);
    }
  }

  if (sat->conflict.size == 0) {
    for (i = 0; i < sat->assumption_lits.size; i++) {
      l = sat->assumption_lits.data[i];
      if (l != null_literal && !int_hset_member(&seen_lits, l)) {
        int_hset_add(&seen_lits, l);
        ivector_push(&sat->conflict, not(l));
      }
    }
  }

  ivector_push(&sat->conflict, null_literal);
  record_theory_conflict(sat->core, sat->conflict.data);

  delete_int_hset(&seen_lits);
  delete_int_hset(&visited);
  delete_int_hset(&labels);
}

/*
 * Run one consistency check in the internal MCSAT context.
 */
static smt_status_t mcsat_satellite_check(mcsat_satellite_t *sat, bool force, bool emit_conflict) {
  model_t mdl;
  smt_status_t status;
  uint64_t sig;
  uint32_t i;
  value_t vtrue;

  if (sat->internal_error < 0) {
    if (emit_conflict) {
      literal_t c[1];
      c[0] = null_literal;
      record_theory_conflict(sat->core, c);
    }
    return YICES_STATUS_UNSAT;
  }

  mcsat_satellite_build_assumptions(sat, false);
  sig = mcsat_satellite_signature(sat);
  if (!force && sat->cache_valid && sat->cache_signature == sig) {
    return YICES_STATUS_SAT;
  }

  init_model(&mdl, sat->mctx.terms, true);
  vtrue = vtbl_mk_bool(&mdl.vtbl, true);
  for (i=0; i<sat->assumptions.size; i++) {
    if (model_find_term_value(&mdl, sat->assumptions.data[i]) == null_value) {
      model_map_term(&mdl, sat->assumptions.data[i], vtrue);
    }
  }

  mcsat_clear(sat->mctx.mcsat);
  mcsat_solve(sat->mctx.mcsat, &sat->params, &mdl, sat->assumptions.size, (const term_t *) sat->assumptions.data);
  status = mcsat_status(sat->mctx.mcsat);

  delete_model(&mdl);

  sat->cache_valid = false;
  if (status == YICES_STATUS_SAT) {
    sat->cache_valid = true;
    sat->cache_signature = sig;
  } else if (status == YICES_STATUS_UNSAT && emit_conflict) {
    mcsat_satellite_record_conflict(sat);
  }

  return status;
}

/*
 * Open one decision level in the eq/diseq activation map.
 */
static void mcsat_satellite_open_level(mcsat_satellite_t *sat) {
  pmap2_push(&sat->eq_active);
  sat->dlevel ++;
  if (sat->eq_level_mark.size <= sat->dlevel) {
    ivector_push(&sat->eq_level_mark, sat->num_eq);
  } else {
    sat->eq_level_mark.data[sat->dlevel] = sat->num_eq;
  }
  sat->cache_valid = false;
}

/*
 * Backtrack eq/diseq activation to target.
 */
static void mcsat_satellite_backtrack_to(mcsat_satellite_t *sat, uint32_t target) {
  while (sat->dlevel > target) {
    sat->num_eq = sat->eq_level_mark.data[sat->dlevel];
    pmap2_pop(&sat->eq_active);
    sat->dlevel --;
  }
  sat->cache_valid = false;
}

/*
 * Align the internal MCSAT scope stack with the outer context base level.
 * This is needed when the satellite is attached after one or more pushes.
 */
static void mcsat_satellite_sync_base_level(mcsat_satellite_t *sat, uint32_t base_level) {
  uint32_t i;

  for (i = 0; i < base_level; i++) {
    context_push(&sat->mctx);
    ivector_push(&sat->atom_push_mark, sat->num_atoms);
    sat->push_depth ++;
    mcsat_satellite_open_level(sat);
  }
}

/*
 * Derive a source literal from a disequality hint if possible.
 */
static literal_t source_lit_from_hint(mcsat_satellite_t *sat, composite_t *hint) {
  literal_t l;

  if (hint == NULL || sat->egraph == NULL) {
    return null_literal;
  }

  l = egraph_occ2literal(sat->egraph, pos_occ(hint->id));
  if (l == null_literal || l == false_literal) {
    return null_literal;
  }

  if (composite_kind(hint) == COMPOSITE_EQ) {
    return not(l);
  }

  return l;
}

/*
 * Add one eq/diseq notification as a labeled internal assumption.
 */
static void mcsat_satellite_add_eq_notification(mcsat_satellite_t *sat, term_t t1, term_t t2, bool eq, literal_t src) {
  int32_t k0, k1;
  pmap2_rec_t *r;
  term_t atom;
  term_t label;
  term_t implication;

  if (t1 > t2) {
    term_t aux = t1;
    t1 = t2;
    t2 = aux;
  }

  k0 = eq ? (int32_t) t1 : -((int32_t) t1) - 1;
  k1 = (int32_t) t2;

  r = pmap2_get(&sat->eq_active, k0, k1);
  if (r->val >= 0) {
    return;
  }

  if (sat->num_eq == sat->eq_size) {
    mcsat_satellite_extend_eq(sat);
  }

  label = mk_uterm(&sat->tm, bool_type(sat->mctx.types));
  atom = eq ? mk_eq(&sat->tm, t1, t2) : mk_neq(&sat->tm, t1, t2);
  implication = mk_implies(&sat->tm, label, atom);
  if (mcsat_satellite_assert_formula(sat, implication) < 0) {
    return;
  }

  sat->eq[sat->num_eq].label = label;
  sat->eq[sat->num_eq].source_lit = src;
  sat->num_eq ++;

  r->val = 1;
  sat->cache_valid = false;
}

/*
 * Control-interface callbacks.
 */
static void mcsat_satellite_start_internalization(void *solver) {
  mcsat_satellite_t *sat = solver;
  sat->cache_valid = false;
}

static void mcsat_satellite_start_search(void *solver) {
  mcsat_satellite_t *sat = solver;
  sat->cache_valid = false;
  if (mcsat_status(sat->mctx.mcsat) != YICES_STATUS_IDLE) {
    mcsat_clear(sat->mctx.mcsat);
  }
}

static bool mcsat_satellite_propagate(void *solver) {
  mcsat_satellite_t *sat = solver;
  smt_status_t status;

  if (!sat->check_in_propagate) {
    return true;
  }

  status = mcsat_satellite_check(sat, false, true);
  return status != YICES_STATUS_UNSAT;
}

static fcheck_code_t mcsat_satellite_final_check(void *solver) {
  mcsat_satellite_t *sat = solver;
  smt_status_t status;

  status = mcsat_satellite_check(sat, false, true);
  switch (status) {
  case YICES_STATUS_UNSAT:
    return FCHECK_CONTINUE;
  case YICES_STATUS_UNKNOWN:
    return FCHECK_UNKNOWN;
  default:
    return FCHECK_SAT;
  }
}

static void mcsat_satellite_increase_decision_level(void *solver) {
  mcsat_satellite_open_level(solver);
}

static void mcsat_satellite_backtrack(void *solver, uint32_t back_level) {
  mcsat_satellite_backtrack_to(solver, back_level);
}

static void mcsat_satellite_push(void *solver) {
  mcsat_satellite_t *sat = solver;
  context_push(&sat->mctx);
  ivector_push(&sat->atom_push_mark, sat->num_atoms);
  sat->push_depth ++;
  mcsat_satellite_open_level(sat);
}

static void mcsat_satellite_pop(void *solver) {
  mcsat_satellite_t *sat = solver;
  uint32_t i;
  int32_t mark;

  assert(sat->push_depth > 0);
  assert(sat->atom_push_mark.size > 0);

  context_pop(&sat->mctx);
  assert(sat->dlevel > 0);

  mark = ivector_pop2(&sat->atom_push_mark);
  for (i=mark; i<sat->num_atoms; i++) {
    sat->atoms[i].active = false;
  }
  sat->push_depth --;
  mcsat_satellite_backtrack_to(sat, sat->dlevel - 1);
}

static void mcsat_satellite_reset(void *solver) {
  mcsat_satellite_t *sat = solver;
  uint32_t i;

  reset_context(&sat->mctx);

  for (i=0; i<sat->num_atoms; i++) {
    if (sat->atoms[i].obj != NULL) {
      safe_free(sat->atoms[i].obj);
      sat->atoms[i].obj = NULL;
    }
  }

  sat->num_atoms = 0;
  sat->num_eq = 0;
  sat->push_depth = 0;
  sat->dlevel = 0;
  sat->cache_valid = false;
  sat->internal_error = 0;

  ivector_reset(&sat->atom_push_mark);
  reset_pmap2(&sat->eq_active);
  ivector_reset(&sat->eq_level_mark);
  ivector_push(&sat->eq_level_mark, 0);

  int_hmap_reset(&sat->arith_var_to_term);
  int_hmap_reset(&sat->label_to_lit);
  ivector_reset(&sat->assumptions);
  ivector_reset(&sat->assumption_lits);
  ivector_reset(&sat->conflict);
}

static void mcsat_satellite_clear(void *solver) {
  mcsat_satellite_t *sat = solver;
  context_clear(&sat->mctx);
  sat->cache_valid = false;
}

/*
 * SMT interface callbacks.
 */
static bool mcsat_satellite_assert_atom(void *solver, void *atom, literal_t l) {
  (void) solver;
  (void) atom;
  (void) l;
  return true;
}

static void mcsat_satellite_expand_explanation(void *solver, literal_t l, void *expl, ivector_t *v) {
  (void) solver;
  (void) l;
  (void) expl;
  (void) v;
}

static literal_t mcsat_satellite_select_polarity(void *solver, void *atom, literal_t l) {
  (void) solver;
  (void) atom;
  return l;
}

/*
 * Egraph interface callbacks.
 */
static void mcsat_satellite_assert_equality(void *solver, thvar_t x1, thvar_t x2, int32_t id) {
  mcsat_satellite_t *sat = solver;
  int_hmap_pair_t *p1, *p2;
  (void) id;

  p1 = int_hmap_find(&sat->arith_var_to_term, x1);
  p2 = int_hmap_find(&sat->arith_var_to_term, x2);
  if (p1 != NULL && p2 != NULL) {
    mcsat_satellite_add_eq_notification(sat, p1->val, p2->val, true, null_literal);
  }
}

static void mcsat_satellite_assert_disequality(void *solver, thvar_t x1, thvar_t x2, composite_t *hint) {
  mcsat_satellite_t *sat = solver;
  int_hmap_pair_t *p1, *p2;
  literal_t src;

  p1 = int_hmap_find(&sat->arith_var_to_term, x1);
  p2 = int_hmap_find(&sat->arith_var_to_term, x2);
  if (p1 != NULL && p2 != NULL) {
    src = source_lit_from_hint(sat, hint);
    mcsat_satellite_add_eq_notification(sat, p1->val, p2->val, false, src);
  }
}

static bool mcsat_satellite_assert_distinct(void *solver, uint32_t n, thvar_t *a, composite_t *hint) {
  mcsat_satellite_t *sat = solver;
  int_hmap_pair_t *p1, *p2;
  literal_t src;
  uint32_t i, j;

  src = source_lit_from_hint(sat, hint);
  for (i=0; i<n; i++) {
    p1 = int_hmap_find(&sat->arith_var_to_term, a[i]);
    if (p1 == NULL) continue;
    for (j=i+1; j<n; j++) {
      p2 = int_hmap_find(&sat->arith_var_to_term, a[j]);
      if (p2 != NULL) {
        mcsat_satellite_add_eq_notification(sat, p1->val, p2->val, false, src);
      }
    }
  }
  return true;
}

static bool mcsat_satellite_check_diseq(void *solver, thvar_t x1, thvar_t x2) {
  (void) solver;
  (void) x1;
  (void) x2;
  return false;
}

static bool mcsat_satellite_is_constant(void *solver, thvar_t x) {
  (void) solver;
  (void) x;
  return false;
}

static void mcsat_satellite_expand_th_expl(void *solver, thvar_t x1, thvar_t x2, void *expl, th_explanation_t *result) {
  (void) solver;
  (void) x1;
  (void) x2;
  (void) expl;
  (void) result;
}

static uint32_t mcsat_satellite_reconcile_model(void *solver, uint32_t max_eq) {
  (void) solver;
  (void) max_eq;
  return 0;
}

static void mcsat_satellite_prepare_model(void *solver) {
  (void) solver;
}

static bool mcsat_satellite_equal_in_model(void *solver, thvar_t x1, thvar_t x2) {
  (void) solver;
  (void) x1;
  (void) x2;
  return false;
}

static void mcsat_satellite_gen_interface_lemma(void *solver, literal_t l, thvar_t x1, thvar_t x2, bool equiv) {
  (void) solver;
  (void) l;
  (void) x1;
  (void) x2;
  (void) equiv;
}

static void mcsat_satellite_release_model(void *solver) {
  (void) solver;
}

static ipart_t *mcsat_satellite_build_partition(void *solver) {
  (void) solver;
  return NULL;
}

static void mcsat_satellite_release_partition(void *solver, ipart_t *partition) {
  (void) solver;
  (void) partition;
}

static void mcsat_satellite_attach_eterm(void *solver, thvar_t x, eterm_t t) {
  (void) solver;
  (void) x;
  (void) t;
}

static eterm_t mcsat_satellite_eterm_of_var(void *solver, thvar_t x) {
  (void) solver;
  (void) x;
  return null_eterm;
}

static literal_t mcsat_satellite_select_eq_polarity(void *solver, thvar_t x, thvar_t y, literal_t l) {
  (void) solver;
  (void) x;
  (void) y;
  return l;
}

/*
 * Static interface records.
 */
static th_ctrl_interface_t mcsat_satellite_ctrl = {
  (start_intern_fun_t) mcsat_satellite_start_internalization,
  (start_fun_t) mcsat_satellite_start_search,
  (propagate_fun_t) mcsat_satellite_propagate,
  (final_check_fun_t) mcsat_satellite_final_check,
  (increase_level_fun_t) mcsat_satellite_increase_decision_level,
  (backtrack_fun_t) mcsat_satellite_backtrack,
  (push_fun_t) mcsat_satellite_push,
  (pop_fun_t) mcsat_satellite_pop,
  (reset_fun_t) mcsat_satellite_reset,
  (clear_fun_t) mcsat_satellite_clear,
};

static th_smt_interface_t mcsat_satellite_smt = {
  (assert_fun_t) mcsat_satellite_assert_atom,
  (expand_expl_fun_t) mcsat_satellite_expand_explanation,
  (select_pol_fun_t) mcsat_satellite_select_polarity,
  NULL,
  NULL,
};

static th_egraph_interface_t mcsat_satellite_eg = {
  (assert_eq_fun_t) mcsat_satellite_assert_equality,
  (assert_diseq_fun_t) mcsat_satellite_assert_disequality,
  (assert_distinct_fun_t) mcsat_satellite_assert_distinct,
  (check_diseq_fun_t) mcsat_satellite_check_diseq,
  (is_constant_fun_t) mcsat_satellite_is_constant,
  (expand_eq_exp_fun_t) mcsat_satellite_expand_th_expl,
  (reconcile_model_fun_t) mcsat_satellite_reconcile_model,
  (prepare_model_fun_t) mcsat_satellite_prepare_model,
  (equal_in_model_fun_t) mcsat_satellite_equal_in_model,
  (gen_inter_lemma_fun_t) mcsat_satellite_gen_interface_lemma,
  (release_model_fun_t) mcsat_satellite_release_model,
  (build_partition_fun_t) mcsat_satellite_build_partition,
  (free_partition_fun_t) mcsat_satellite_release_partition,
  (attach_to_var_fun_t) mcsat_satellite_attach_eterm,
  (get_eterm_fun_t) mcsat_satellite_eterm_of_var,
  (select_eq_polarity_fun_t) mcsat_satellite_select_eq_polarity,
};


/*
 * Constructor/destructor.
 */
mcsat_satellite_t *new_mcsat_satellite(context_t *ctx) {
  mcsat_satellite_t *sat;

  sat = (mcsat_satellite_t *) safe_malloc(sizeof(mcsat_satellite_t));

  sat->ctx = ctx;
  sat->core = ctx->core;
  sat->egraph = ctx->egraph;

  init_context(&sat->mctx, ctx->terms, ctx->logic, CTX_MODE_PUSHPOP, CTX_ARCH_MCSAT, false);
  sat->mctx.mcsat_options = ctx->mcsat_options;
  sat->mctx.mcsat_options.model_interpolation = true;
  ivector_copy(&sat->mctx.mcsat_var_order, ctx->mcsat_var_order.data, ctx->mcsat_var_order.size);
  ivector_copy(&sat->mctx.mcsat_initial_var_order, ctx->mcsat_initial_var_order.data, ctx->mcsat_initial_var_order.size);

  init_term_manager(&sat->tm, sat->mctx.terms);

  init_params_to_defaults(&sat->params);
  sat->check_in_propagate = true;

  sat->internal_error = 0;

  sat->cache_valid = false;
  sat->cache_signature = 0;

  sat->atoms = NULL;
  sat->num_atoms = 0;
  sat->atom_size = 0;
  sat->push_depth = 0;
  init_ivector(&sat->atom_push_mark, 0);

  init_int_hmap(&sat->arith_var_to_term, 0);

  sat->eq = NULL;
  sat->num_eq = 0;
  sat->eq_size = 0;
  sat->dlevel = 0;
  init_pmap2(&sat->eq_active);
  init_ivector(&sat->eq_level_mark, 8);
  ivector_push(&sat->eq_level_mark, 0);

  init_ivector(&sat->assumptions, 0);
  init_ivector(&sat->assumption_lits, 0);
  init_int_hmap(&sat->label_to_lit, 0);
  init_ivector(&sat->conflict, 0);

  if (ctx->trace != NULL) {
    mcsat_satellite_set_trace(sat, ctx->trace);
  }

  mcsat_satellite_sync_base_level(sat, ctx->base_level);

  return sat;
}

void delete_mcsat_satellite(mcsat_satellite_t *sat) {
  uint32_t i;

  if (sat == NULL) {
    return;
  }

  for (i = 0; i < sat->num_atoms; i++) {
    if (sat->atoms[i].obj != NULL) {
      safe_free(sat->atoms[i].obj);
      sat->atoms[i].obj = NULL;
    }
  }
  safe_free(sat->atoms);
  sat->atoms = NULL;

  safe_free(sat->eq);
  sat->eq = NULL;

  delete_ivector(&sat->conflict);
  delete_int_hmap(&sat->label_to_lit);
  delete_ivector(&sat->assumption_lits);
  delete_ivector(&sat->assumptions);

  delete_ivector(&sat->eq_level_mark);
  delete_pmap2(&sat->eq_active);

  delete_int_hmap(&sat->arith_var_to_term);
  delete_ivector(&sat->atom_push_mark);

  delete_term_manager(&sat->tm);
  delete_context(&sat->mctx);
  safe_free(sat);
}


/*
 * Public interface getters.
 */
th_ctrl_interface_t *mcsat_satellite_ctrl_interface(mcsat_satellite_t *sat) {
  (void) sat;
  return &mcsat_satellite_ctrl;
}

th_smt_interface_t *mcsat_satellite_smt_interface(mcsat_satellite_t *sat) {
  (void) sat;
  return &mcsat_satellite_smt;
}

th_egraph_interface_t *mcsat_satellite_egraph_interface(mcsat_satellite_t *sat) {
  (void) sat;
  return &mcsat_satellite_eg;
}

int32_t mcsat_satellite_assert_formulas(mcsat_satellite_t *sat, uint32_t n, const term_t *a) {
  uint32_t i;
  int32_t code;

  for (i = 0; i < n; i++) {
    code = mcsat_satellite_assert_formula(sat, a[i]);
    if (code < 0) {
      return code;
    }
  }

  return CTX_NO_ERROR;
}

/*
 * Register one tracked unsupported atom.
 */
int32_t mcsat_satellite_register_atom(mcsat_satellite_t *sat, term_t atom, literal_t l, void **obj) {
  mcsat_atom_entry_t *entry;
  term_t plabel, nlabel;
  term_t implication;
  int32_t code;
  mcsat_atom_object_t *atom_obj;
  uint32_t i;

  assert(l >= 0);

  // Already tracked: keep the existing object/literal association.
  for (i = 0; i < sat->num_atoms; i++) {
    entry = sat->atoms + i;
    if (entry->atom == atom && entry->lit == l) {
      if (obj != NULL) {
        *obj = entry->obj;
      }
      return CTX_NO_ERROR;
    }
  }

  if (sat->num_atoms == sat->atom_size) {
    mcsat_satellite_extend_atoms(sat);
  }

  plabel = mk_uterm(&sat->tm, bool_type(sat->mctx.types));
  nlabel = mk_uterm(&sat->tm, bool_type(sat->mctx.types));

  implication = mk_implies(&sat->tm, plabel, atom);
  code = mcsat_satellite_assert_formula(sat, implication);
  if (code < 0) {
    return code;
  }

  implication = mk_implies(&sat->tm, nlabel, not(atom));
  code = mcsat_satellite_assert_formula(sat, implication);
  if (code < 0) {
    return code;
  }

  atom_obj = NULL;
  if (obj != NULL) {
    atom_obj = safe_malloc(sizeof(mcsat_atom_object_t));
    atom_obj->id = sat->num_atoms;
    *obj = atom_obj;
  }

  entry = sat->atoms + sat->num_atoms;
  entry->atom = atom;
  entry->lit = l;
  entry->pos_label = plabel;
  entry->neg_label = nlabel;
  entry->obj = atom_obj;
  entry->active = true;
  sat->num_atoms ++;

  sat->cache_valid = false;
  return CTX_NO_ERROR;
}

/*
 * Register thvar -> term for arithmetic terms.
 */
void mcsat_satellite_register_arith_term(mcsat_satellite_t *sat, thvar_t x, term_t t) {
  int_hmap_pair_t *p;
  p = int_hmap_get(&sat->arith_var_to_term, x);
  p->val = t;
}

/*
 * Parameters/tracing/model/GC support.
 */
void mcsat_satellite_set_search_parameters(mcsat_satellite_t *sat, const param_t *params) {
  sat->params = *params;
  sat->check_in_propagate = (params->mcsat_supplement_check == MCSAT_SUPPLEMENT_CHECK_BOTH);
  sat->cache_valid = false;
}

void mcsat_satellite_set_trace(mcsat_satellite_t *sat, tracer_t *trace) {
  mcsat_set_tracer(sat->mctx.mcsat, trace);
}

term_t mcsat_satellite_get_unsat_model_interpolant(mcsat_satellite_t *sat) {
  return mcsat_get_unsat_model_interpolant(sat->mctx.mcsat);
}

void mcsat_satellite_set_unsat_model_interpolant(mcsat_satellite_t *sat, term_t t) {
  mcsat_set_unsat_result(sat->mctx.mcsat, t);
}

term_t mcsat_satellite_compute_unsat_model_interpolant(mcsat_satellite_t *sat, const param_t *params, uint32_t n, const term_t *a) {
  ivector_t labels;
  ivector_t assumptions;
  term_manager_t tm;
  model_t mdl;
  value_t vtrue;
  term_t result;
  smt_status_t status;
  uint32_t i;
  bool pushed;

  if (sat->internal_error < 0) {
    return NULL_TERM;
  }

  init_ivector(&labels, n);
  init_ivector(&assumptions, n);
  init_term_manager(&tm, sat->mctx.terms);
  init_model(&mdl, sat->mctx.terms, true);

  pushed = false;
  result = NULL_TERM;

  /*
   * Internal push requires an idle MCSAT state in debug builds.
   * This path may be called after a previous UNSAT check.
   */
  if (mcsat_status(sat->mctx.mcsat) != YICES_STATUS_IDLE) {
    mcsat_clear(sat->mctx.mcsat);
  }

  if (context_supports_pushpop(&sat->mctx)) {
    context_push(&sat->mctx);
    pushed = true;
  }

  vtrue = vtbl_mk_bool(&mdl.vtbl, true);

  for (i = 0; i < n; i++) {
    term_t b, implication;
    int32_t code;

    b = new_uninterpreted_term(sat->mctx.terms, bool_id);
    implication = mk_implies(&tm, b, a[i]);
    code = mcsat_satellite_assert_formula(sat, implication);
    if (code < 0) {
      goto done;
    }

    ivector_push(&labels, b);
    ivector_push(&assumptions, b);
    model_map_term(&mdl, b, vtrue);
  }

  mcsat_clear(sat->mctx.mcsat);
  mcsat_solve(sat->mctx.mcsat, params != NULL ? params : &sat->params, &mdl,
              assumptions.size, (const term_t *) assumptions.data);
  status = mcsat_status(sat->mctx.mcsat);

  if (status == YICES_STATUS_UNSAT) {
    term_t raw = mcsat_get_unsat_model_interpolant(sat->mctx.mcsat);
    if (raw == NULL_TERM) {
      raw = false_term;
    }
    if (labels.size > 0) {
      term_subst_t subst;
      init_term_subst(&subst, &tm, labels.size, labels.data, a);
      result = apply_term_subst(&subst, raw);
      delete_term_subst(&subst);
    } else {
      result = raw;
    }
  }

done:
  delete_model(&mdl);
  delete_term_manager(&tm);
  delete_ivector(&assumptions);
  delete_ivector(&labels);

  if (pushed) {
    mcsat_cleanup_assumptions(sat->mctx.mcsat);
    context_pop(&sat->mctx);
  }

  if (result != NULL_TERM) {
    mcsat_set_unsat_result(sat->mctx.mcsat, result);
  }

  return result;
}

void mcsat_satellite_build_model(mcsat_satellite_t *sat, model_t *model) {
  model_t mdl;
  smt_status_t status;
  uint32_t i;
  value_t vtrue;

  if (sat->internal_error < 0) {
    return;
  }

  /*
   * For model construction, complete unassigned tracked literals with their
   * current polarity hint so MCSAT can compute a concrete witness model.
   */
  mcsat_satellite_build_assumptions(sat, true);

  init_model(&mdl, sat->mctx.terms, true);
  vtrue = vtbl_mk_bool(&mdl.vtbl, true);
  for (i = 0; i < sat->assumptions.size; i++) {
    if (model_find_term_value(&mdl, sat->assumptions.data[i]) == null_value) {
      model_map_term(&mdl, sat->assumptions.data[i], vtrue);
    }
  }

  mcsat_clear(sat->mctx.mcsat);
  mcsat_solve(sat->mctx.mcsat, &sat->params, &mdl, sat->assumptions.size, (const term_t *) sat->assumptions.data);
  status = mcsat_status(sat->mctx.mcsat);

  delete_model(&mdl);

  if (status == YICES_STATUS_SAT) {
    mcsat_build_model(sat->mctx.mcsat, model);
  }
}

void mcsat_satellite_gc_mark(mcsat_satellite_t *sat) {
  uint32_t i;

  for (i=0; i<sat->num_atoms; i++) {
    term_table_set_gc_mark(sat->mctx.terms, index_of(sat->atoms[i].atom));
    term_table_set_gc_mark(sat->mctx.terms, index_of(sat->atoms[i].pos_label));
    term_table_set_gc_mark(sat->mctx.terms, index_of(sat->atoms[i].neg_label));
  }

  for (i=0; i<sat->num_eq; i++) {
    term_table_set_gc_mark(sat->mctx.terms, index_of(sat->eq[i].label));
  }

  mcsat_gc_mark(sat->mctx.mcsat);
}
