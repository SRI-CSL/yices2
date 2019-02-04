/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "bv_explainer.h"

#include "bv_slicing.h"
#include "bv_evaluator.h"
#include "bv_utils.h"

#include "context/context_types.h"

#include "mcsat/variable_db.h"
#include "mcsat/tracing.h"
#include "mcsat/utils/int_mset.h"
#include "mcsat/utils/substitution.h"
#include "mcsat/eq/equality_graph.h"

#include "utils/int_array_sort2.h"

#include "yices.h"

#include <inttypes.h>

static
const char* bv_kind_to_string(bv_kind_type_t kt) {
  switch (kt) {
  case BV_KIND_EQ: return "equality";
  case BV_KIND_EXT_CON: return "extract/concat";
  case BV_KIND_BOOL2BV: return "bool-to-bv";
  case BV_KIND_BITWISE: return "bitwise";
  case BV_KIND_SHIFT: return "shifts";
  case BV_KIND_ARITH_CMP: return "comparison";
  case BV_KIND_ARITH_POLY: return "arithmetic";
  default:
      assert(false);
  }
  return "unknown";
}

static
const char* subtheory_to_string(bv_subtheory_t th) {
  switch (th) {
    case BV_TH_EQ: return "equality";
    case BV_TH_EQ_EXT_CON: return "eq/extract/concat";
    case BV_TH_FULL: return "full";
    default:
      assert(false);
  }
  return "unknown";
}

int bv_th_eq[BV_KIND_COUNT] = {
    1, // BV_KIND_EQ = 0,
    0, // BV_KIND_EXT_CON,
    0, // BV_KIND_BOOL2BV,
    0, // BV_KIND_BITWISE,
    0, // BV_KIND_SHIFT,
    0, // BV_KIND_ARITH_CMP,
    0, // BV_KIND_ARITH_POLY
};

int bv_th_eq_ext_con[BV_KIND_COUNT] = {
    1, // BV_KIND_EQ = 0,
    1, // BV_KIND_EXT_CON,
    0, // BV_KIND_BOOL2BV,
    0, // BV_KIND_BITWISE,
    0, // BV_KIND_SHIFT,
    0, // BV_KIND_ARITH_CMP,
    0, // BV_KIND_ARITH_POLY
};

/** Match the counts with template. If count > 0 then corresponding template must be 1 to match */
bool bv_kinds_match(const int* kind_counts, const int* kind_template) {
  uint32_t i;
  for (i = 0; i < BV_KIND_COUNT; ++ i) {
    if (kind_counts[i] > 0 && kind_template[i] == 0) {
      return false;
    }
  }
  return true;
}

void bv_explainer_construct(bv_explainer_t* exp, plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {
  exp->ctx = ctx;
  exp->tm = &ctx->var_db->tm;
  exp->wlm = wlm;
  exp->eval = eval;

  init_int_hset(&exp->visited_cache, 0);
  init_ivector(&exp->tmp_conflict_vec, 0);

  exp->stats.th_eq = statistics_new_int(exp->ctx->stats, "mcsat::bv::conflicts_eq");
  exp->stats.th_eq_ext_con = statistics_new_int(exp->ctx->stats, "mcsat::bv::conflict_eq_ext_con");
  exp->stats.th_full = statistics_new_int(exp->ctx->stats, "mcsat::bv::conflicts_full");
}

void bv_explainer_destruct(bv_explainer_t* exp) {
  delete_int_hset(&exp->visited_cache);
  delete_ivector(&exp->tmp_conflict_vec);
}

static
void bv_explainer_count_kinds(bv_explainer_t* exp, term_t t, int* kinds_count) {

  assert(is_pos_term(t));

  // SKip if already visited
  if (int_hset_member(&exp->visited_cache, t)) {
    return;
  }

  // The term table
  term_table_t* terms = exp->ctx->terms;

  term_kind_t kind = term_kind(terms, t);
  switch (kind) {
  case CONSTANT_TERM:
  case BV_CONSTANT:
  case BV64_CONSTANT:
    // Nothing to do really
    break;
  case EQ_TERM: {
    // Equality. Belongs to all sub-theories
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    term_t t0 = atom_comp->arg[0], t0_pos = unsigned_term(t0);
    if (t0 != t0_pos) kinds_count[BV_KIND_BITWISE] ++;
    term_t t1 = atom_comp->arg[1], t1_pos = unsigned_term(t1);
    if (t1 != t1_pos) kinds_count[BV_KIND_BITWISE] ++;
    bv_explainer_count_kinds(exp, t0_pos, kinds_count);
    bv_explainer_count_kinds(exp, t1_pos, kinds_count);
    kinds_count[BV_KIND_EQ] ++;
    break;
  }
  case BV_EQ_ATOM: {
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    bv_explainer_count_kinds(exp, atom_comp->arg[0], kinds_count);
    bv_explainer_count_kinds(exp, atom_comp->arg[1], kinds_count);
    kinds_count[BV_KIND_EQ] ++;
    break;
  }
  case BV_GE_ATOM:
  case BV_SGE_ATOM: {
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    bv_explainer_count_kinds(exp, atom_comp->arg[0], kinds_count);
    bv_explainer_count_kinds(exp, atom_comp->arg[1], kinds_count);
    kinds_count[BV_KIND_ARITH_CMP] ++;
    break;
  }
  case BV_ARRAY: {
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    for (uint32_t i = 0; i < concat_desc->arity; ++ i) {
      term_t t_i = concat_desc->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      if (t_i != t_i_pos) kinds_count[BV_KIND_BITWISE] ++;
      switch (term_kind(terms, t_i_pos)) {
      case EQ_TERM:
      case BV_EQ_ATOM:
      case BV_GE_ATOM:
      case BV_SGE_ATOM:
      case OR_TERM:
      case XOR_TERM:
      case VARIABLE:
      case UNINTERPRETED_TERM:
      case DISTINCT_TERM: {
        kinds_count[BV_KIND_BOOL2BV] ++;
      }
      default:
        bv_explainer_count_kinds(exp, t_i_pos, kinds_count);
      }
    }
    kinds_count[BV_KIND_EXT_CON] ++;
    break;
  }
  case OR_TERM: {
    composite_term_t* t_comp = or_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      term_t t_i = t_comp->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      bv_explainer_count_kinds(exp, t_i_pos, kinds_count);
    }
    kinds_count[BV_KIND_BITWISE] ++;
    break;
  }
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:{
    composite_term_t* t_comp = composite_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      bv_explainer_count_kinds(exp, t_comp->arg[i], kinds_count);
    }
    kinds_count[BV_KIND_ARITH_POLY] ++;
    break;
  }
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR: {
    composite_term_t* t_comp = composite_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      bv_explainer_count_kinds(exp, t_comp->arg[i], kinds_count);
    }
    kinds_count[BV_KIND_SHIFT] ++;
    break;
  }
  case BIT_TERM:
    bv_explainer_count_kinds(exp, bit_term_arg(terms, t), kinds_count);
    kinds_count[BV_KIND_EXT_CON] ++;
    break;
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_explainer_count_kinds(exp, t_poly->mono[i].var, kinds_count);
    }
    kinds_count[BV_KIND_ARITH_POLY] ++;
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_explainer_count_kinds(exp, t_poly->mono[i].var, kinds_count);
    }
    kinds_count[BV_KIND_ARITH_POLY] ++;
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* t_pprod = pprod_term_desc(terms, t);
    for (uint32_t i = 0; i < t_pprod->len; ++ i) {
      bv_explainer_count_kinds(exp, t_pprod->prod[i].var, kinds_count);
    }
    kinds_count[BV_KIND_ARITH_POLY] ++;
    break;
  }
  default:
    // A variable or a foreign term
    assert(is_pos_term(t));
  }

  // Mark as visited
  int_hset_add(&exp->visited_cache, t);
}

bv_subtheory_t bv_explainer_get_subtheory(bv_explainer_t* exp, const ivector_t* conflict) {

  uint32_t i;

  const variable_db_t* var_db = exp->ctx->var_db;

  // Reset the cache
  int_hset_reset(&exp->visited_cache);

  // Get the kinds
  int kind_count[BV_KIND_COUNT] = { 0 };
  for (i = 0; i < conflict->size; i ++) {
    term_t t = variable_db_get_term(var_db, conflict->data[i]);
    bv_explainer_count_kinds(exp, t, kind_count);
  }

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
    bv_kind_type_t bv_kind;
    FILE* out = ctx_trace_out(exp->ctx);
    fprintf(out, "kinds:\n");
    for (bv_kind = 0; bv_kind < BV_KIND_COUNT; ++ bv_kind) {
      if (kind_count[bv_kind] > 0) {
        fprintf(out, "%s\n", bv_kind_to_string(bv_kind));
      }
    }
  }

  // Decide which theory it is
  if (bv_kinds_match(kind_count, bv_th_eq)) {
    return BV_TH_EQ;
  }
  if (bv_kinds_match(kind_count, bv_th_eq_ext_con)) {
    return BV_TH_EQ_EXT_CON;
  }

  return BV_TH_FULL;
}

typedef struct {

  /** The substitution */
  substitution_t subst;

  /** The terms to assign (old terms, not new) */
  ivector_t vars_to_assign;

  /** MCSAT plugin context */
  plugin_context_t* ctx;

  /** Yices config */
  ctx_config_t* config;

  /** Yices context */
  context_t* yices_ctx;

} bv_core_solver_t;

void bv_core_solver_construct(bv_core_solver_t* solver, plugin_context_t* ctx) {
  substitution_construct(&solver->subst, &ctx->var_db->tm, ctx->tracer);
  init_ivector(&solver->vars_to_assign, 0);
  solver->ctx = ctx;

  // Create an instance of Yices
  solver->config = yices_new_config();
  int32_t ret = yices_default_config_for_logic(solver->config, "QF_BV");
  (void) ret;
  assert(ret == 0);
  solver->yices_ctx = yices_new_context(solver->config);
  assert (solver->yices_ctx != NULL);
}

void bv_core_solver_destruct(bv_core_solver_t* solver) {
  substitution_destruct(&solver->subst);
  delete_ivector(&solver->vars_to_assign);

  // Delete the yices instance
  yices_free_context(solver->yices_ctx);
  yices_free_config(solver->config);
}

void bv_core_solver_add_variable(bv_core_solver_t* solver, variable_t var, bool with_value) {
  // Add new variable to substitute
  term_t var_term = variable_db_get_term(solver->ctx->var_db, var);
  if (!substitution_has_term(&solver->subst, var_term)) {
    if (ctx_trace_enabled(solver->ctx, "mcsat::bv::conflict")) {
      FILE* out = ctx_trace_out(solver->ctx);
      fprintf(out, "Variable: ");
      ctx_trace_term(solver->ctx, var_term);
    }
    // Make a fresh variable if not already a variable
    term_t var_fresh;
    term_kind_t kind = term_kind(solver->yices_ctx->terms, var_term);
    if (kind != UNINTERPRETED_TERM) {
      type_t var_type = yices_type_of_term(var_term);
      var_fresh = yices_new_uninterpreted_term(var_type);
    } else {
      var_fresh = var_term;
    }
    substitution_add(&solver->subst, var_term, var_fresh);
    // If to be assigned, remember it
    if (with_value) {
      ivector_push(&solver->vars_to_assign, var);
    }
  }
}

/**
 * Run the substitution and assert (with the same polarity as in MCSAT)
 */
void bv_solver_assert(bv_core_solver_t* solver, variable_t var) {
  term_t assertion_term = variable_db_get_term(solver->ctx->var_db, var);
  const mcsat_value_t* var_value = trail_get_value(solver->ctx->trail, var);
  assert(var_value->type == VALUE_BOOLEAN);
  if (!var_value->b) {
    assertion_term = opposite_term(assertion_term);
  }
  assertion_term = substitution_run_fwd(&solver->subst, assertion_term, 0);
  if (ctx_trace_enabled(solver->ctx, "mcsat::bv::conflict")) {
    FILE* out = trace_out(solver->yices_ctx->trace);
    ctx_trace_term(solver->ctx, assertion_term);
    fprintf(out, "  previously \n");
    ctx_trace_term(solver->ctx, assertion_term);
  }
  yices_assert_formula(solver->yices_ctx, assertion_term);
}

bool bv_solver_cmp_var_by_trail_index(void *data, variable_t t1, variable_t t2) {
  const mcsat_trail_t* trail = data;
  assert(trail_has_value(trail, t1));
  assert(trail_has_value(trail, t2));
  return trail_get_index(trail, t1) < trail_get_index(trail, t2);
}

void bv_solver_solve_and_get_core(bv_core_solver_t* solver, term_vector_t* core) {

  plugin_context_t* ctx = solver->ctx;
  const variable_db_t* var_db = ctx->var_db;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm = &solver->ctx->var_db->tm;

  // Vector to store assumptions
  ivector_t assumptions;
  init_ivector(&assumptions, 0);

  // Sort variables to assign according to their trail index
  // int_array_sort2(solver->vars_to_assign.data, solver->vars_to_assign.size, (void*) solver->ctx->trail, bv_solver_cmp_var_by_trail_index);

  // Make assumptions
  uint32_t i, bit;
  for (i = 0; i < solver->vars_to_assign.size; ++ i) {
    // Variable and its value
    variable_t var = solver->vars_to_assign.data[i];
    const mcsat_value_t* var_value = trail_get_value(trail, var);
    assert(var_value->type == VALUE_BOOLEAN || var_value->type == VALUE_BV);
    // Get the term, and it's substitution
    term_t var_term = variable_db_get_term(var_db, var);
    term_t var_term_subst = substitution_run_fwd(&solver->subst, var_term, 0);
    if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
      FILE* out = trace_out(solver->yices_ctx->trace);
      ctx_trace_term(ctx, var_term_subst);
      fprintf(out, "  -> ");
      mcsat_value_print(var_value, out);
      fprintf(out, "\n");
    }
    if (var_value->type == VALUE_BOOLEAN) {
      // Boolean variables, just add as assertion
      bool bool_value = var_value->b;
      if (!bool_value) var_term_subst = opposite_term(var_term_subst);
      ivector_push(&assumptions, var_term_subst);
    } else {
      // Bitvector variables
      const bvconstant_t* bv_value = &var_value->bv_value;
      // Assert individual bits
      for (bit = 0; bit < bv_value->bitsize; bit ++) {
        // Extract bit
        term_t bit_assertion = mk_bitextract(tm, var_term_subst, bit);
        // Assert appropriate value
        bool bool_value = bvconst_tst_bit(bv_value->data, bit);
        if (!bool_value) bit_assertion = opposite_term(bit_assertion);
        ivector_push(&assumptions, bit_assertion);
      }
    }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Solving with assumptions: \n");
    for (i = 0; i < assumptions.size; ++ i) {
      ctx_trace_term(ctx, assumptions.data[i]);
    }
  }

  // Check the assumptions (should be unsat)
  smt_status_t status = yices_check_context_with_assumptions(solver->yices_ctx, NULL, assumptions.size, assumptions.data);
  (void) status;
  assert(status == STATUS_UNSAT);

  // Get the unsat core
  int32_t ret = yices_get_unsat_core(solver->yices_ctx, core);
  (void) ret;
  assert(ret == 0);

  // Substitute the core back to internal
  for (i = 0; i < core->size; ++ i) {
    term_t t = core->data[i];
    t = substitution_run_bck(&solver->subst, t, 0);
    core->data[i] = t;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Core: \n");
    for (i = 0; i < core->size; ++ i) {
      ctx_trace_term(ctx, core->data[i]);
    }
  }

  // Remove assumption vector
  delete_ivector(&assumptions);
}

static
void bv_explainer_get_conflict_all_simple(bv_explainer_t* exp, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {
  uint32_t i;
  variable_t atom_i_var;
  term_t atom_i_term;
  bool atom_i_value;

  const variable_db_t* var_db = exp->ctx->var_db;
  const mcsat_trail_t* trail = exp->ctx->trail;

  (*exp->stats.th_full) ++;

  // Simple conflict resolution: get the variables and say x != v
  int_mset_t assigned_vars;
  int_mset_construct(&assigned_vars, 0);
  for (i = 0; i < conflict_core->size; ++ i) {
    atom_i_var = conflict_core->data[i];
    atom_i_term = variable_db_get_term(var_db, atom_i_var);
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    // Add atom to conflict
    if (atom_i_value) {
      ivector_push(conflict, atom_i_term);
    } else {
      ivector_push(conflict, opposite_term(atom_i_term));
    }
    // Add subvariables to set
    variable_list_ref_t list_ref = watch_list_manager_get_list_of(exp->wlm, atom_i_var);
    variable_t* atom_i_vars = watch_list_manager_get_list(exp->wlm, list_ref);
    for (; *atom_i_vars != variable_null; atom_i_vars ++) {
      if (*atom_i_vars != atom_i_var) {
        assert(*atom_i_vars == conflict_var || trail_has_value(trail, *atom_i_vars));
        if (*atom_i_vars != conflict_var) {
          int_mset_add(&assigned_vars, *atom_i_vars);
        }
      }
    }
  }

  const ivector_t* assigned_vars_vec = int_mset_get_list(&assigned_vars);
  for (i = 0; i < assigned_vars_vec->size; ++i) {
    variable_t var = assigned_vars_vec->data[i];
    term_t var_term = variable_db_get_term(var_db, var);
    if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
      ctx_trace_printf(exp->ctx, "vars:\n");
      ctx_trace_printf(exp->ctx, "[%"PRIu32"]: ", i);
      ctx_trace_term(exp->ctx, var_term);
    }
    const mcsat_value_t* value = trail_get_value(trail, var);
    if (value->type == VALUE_BOOLEAN) {
      if (value->b) {
        ivector_push(conflict, var_term);
      } else {
        ivector_push(conflict, opposite_term(var_term));
      }
    } else if (value->type == VALUE_BV) {
      term_t var_value = mk_bv_constant(exp->tm, (bvconstant_t*) &value->bv_value);
      term_t var_eq_value = mk_eq(exp->tm, var_term, var_value);
      ivector_push(conflict, var_eq_value);
    } else {
      assert(false);
    }
  }

  int_mset_destruct(&assigned_vars);
}

void bv_explainer_get_conflict_all_with_yices(bv_explainer_t* exp, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {
  uint32_t i;

  exp->stats.th_full ++;

  const variable_db_t* var_db = exp->ctx->var_db;
  const mcsat_trail_t* trail = exp->ctx->trail;

  // Initialize the substitution
  bv_core_solver_t solver;
  bv_core_solver_construct(&solver, exp->ctx);

  // Get the assigned variables into a set and copy assertions into explanation
  for (i = 0; i < conflict_core->size; ++ i) {
    // Get assigned variables
    variable_t atom_i_var = conflict_core->data[i];
    variable_list_ref_t list_ref = watch_list_manager_get_list_of(exp->wlm, atom_i_var);
    variable_t* atom_i_vars = watch_list_manager_get_list(exp->wlm, list_ref);
    for (; *atom_i_vars != variable_null; atom_i_vars ++) {
      variable_t var = *atom_i_vars;
      if (var != atom_i_var) {
        bool assign_value = (var != conflict_var);
        bv_core_solver_add_variable(&solver, var, assign_value);
      }
    }
    // Copy into explanation
    const mcsat_value_t* atom_i_value = trail_get_value(trail, atom_i_var);
    assert(atom_i_value != NULL && atom_i_value->type == VALUE_BOOLEAN);
    term_t assertion = variable_db_get_term(var_db, atom_i_var);
    if (!atom_i_value->b) { assertion = opposite_term(assertion); }
    ivector_push(conflict, assertion);
  }

  // Now assert the conflict
  for (i = 0; i < conflict_core->size; ++ i) {
    variable_t assertion_var = conflict_core->data[i];
    bv_solver_assert(&solver, assertion_var);
  }

  // Solve and get the core
  term_vector_t core;
  yices_init_term_vector(&core);
  bv_solver_solve_and_get_core(&solver, &core);

  // Copy over the core
  for (i = 0; i < core.size; ++ i) {
    ivector_push(conflict, core.data[i]);
  }

  // Delete stuff
  yices_delete_term_vector(&core);
  bv_core_solver_destruct(&solver);
}

void bv_explainer_get_conflict_eq_ext_con(bv_explainer_t* exp, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {

  (*exp->stats.th_eq_ext_con) ++;

  plugin_context_t* ctx = exp->ctx;

  term_table_t* terms   = ctx->terms;
  term_manager_t* tm = &ctx->var_db->tm;

  // The output conflict always contains the conflict core:
  for (uint32_t i = 0; i < conflict_core->size; i++) {
    variable_t atom_var = conflict_core->data[i];
    term_t t = variable_db_get_term(ctx->var_db, atom_var);
    bool value = trail_get_boolean_value(ctx->trail, atom_var);
    ivector_push(conflict, value?t:opposite_term(t));
  }

  // Create the equality graph
  eq_graph_t eq_graph;
  eq_graph_construct(&eq_graph, exp->ctx, "mcsat::bv::conflict");

  // Do the slicing
  bv_slicing_t slicing;
  bv_slicing_construct(&slicing, ctx, conflict_core, &eq_graph);
    
  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
    bv_slicing_print_slicing(&slicing);
  }

  // SMT'2017 paper

  spair_t* p;
  splist_t* current = slicing.constraints[0];

  // We send the equalities to the e-graph
  while (current != NULL) {
    assert(current->is_main);
    p = current->pair;
    if (p->lhs->base.slice_term != p->rhs->base.slice_term) {
      eq_graph_assert_term_eq(&eq_graph, p->lhs->base.slice_term, p->rhs->base.slice_term, 0);
      // 0 means that the assertion is a consequence of the conflict_core
      // We have use higher numbers when we put slice assignments s[j:i] <- v in the egraph
    }
    current = current->next;
  }
  
  ivector_t reasons; // where we collect the reasons why things happen in the e-graph
  init_ivector(&reasons,0);
  ivector_t reasons_types; // ...together with their associated types
  init_ivector(&reasons_types,0); // (i.e. why they are in the e-graph)
  
  // Case 1: conflict in e-graph
  if (eq_graph.in_conflict) { // Get conflict from e-graph
    if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Conflict in egraph\n");
    }
    eq_graph_get_conflict(&eq_graph, &reasons, &reasons_types, NULL);
  } else { // e-graph not in conflict

    ivector_t interface_terms; // where we collect interface terms
    init_ivector(&interface_terms,0);

    // We go through the disjunctions of disequalities
    for (uint32_t i = 1; i < slicing.nconstraints; i++) {

      current = slicing.constraints[i]; // Get disjunction number i
      if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Looking at disjunction %d:\n",i);
      }
      // Go through disjuncts
      while (current != NULL) {
        p = current->pair;
        assert(p->appearing_in == i); // Check that this is indeed the right disequality
        term_t lhs = p->lhs->base.slice_term;
        term_t rhs = p->rhs->base.slice_term;

        if (lhs == rhs
            || (eq_graph_has_term(&eq_graph, lhs)
                && eq_graph_has_term(&eq_graph, rhs)
                && eq_graph_are_equal(&eq_graph, lhs, rhs))) {
          // adding the reason why this disequality is false
          if (lhs != rhs) {
            eq_graph_explain_eq(&eq_graph, lhs, rhs, &reasons, &reasons_types, NULL);
          }
          if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "Looking at why disequality ");
            term_print_to_file(out, terms, lhs);            
            fprintf(out, " != ");
            term_print_to_file(out, terms, rhs);
            fprintf(out, " is false: ");
            for (uint32_t i = 0; i < reasons.size; i++) {
              if (i>0) fprintf(out,", ");
              fprintf(out,"%d", reasons.data[i]);
              if (reasons.data[i] !=0) {
                fprintf(out," [");
                term_print_to_file(out, terms, reasons.data[i]);
                fprintf(out,"]");
              }
            }
            fprintf(out,"\n");
          }
        }
        else{
          // We need to collect the interface term
          if (eq_graph_has_term(&eq_graph, lhs)
              && eq_graph_term_has_value(&eq_graph, lhs)){
            term_t iterm = eq_graph_explain_term_propagation(&eq_graph, lhs, &reasons, &reasons_types, NULL);
            term_kind_t kind = term_kind(terms, iterm);
            if (kind != BV64_CONSTANT && kind != BV_CONSTANT) {
              ivector_push(&interface_terms, iterm);
              if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
                FILE* out = ctx_trace_out(ctx);
                fprintf(out, "Just added left interface term ");
                term_print_to_file(out, terms, iterm);
                fprintf(out, "\n");
              }
            }
          }
          if (eq_graph_has_term(&eq_graph, rhs)
              && eq_graph_term_has_value(&eq_graph, rhs)){
            term_t iterm = eq_graph_explain_term_propagation(&eq_graph, rhs, &reasons, &reasons_types, NULL);
            term_kind_t kind = term_kind(terms, iterm);
            if (kind != BV64_CONSTANT && kind != BV_CONSTANT) {
              ivector_push(&interface_terms, iterm);
              if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
                FILE* out = ctx_trace_out(ctx);
                fprintf(out, "Just added right interface term ");
                term_print_to_file(out, terms, iterm);
                fprintf(out, "\n");
              }
            }
          }
          // Note that both "ifs" cannnot be true at the same time, otherwise the disequality could be evaluated:
          // if it evaluates to true, then the disjunction would evaluate to true, so the constraint from whence it came would not be in the core
          // if it evaluates to false, then lhs and rhs would be in the same class of the graph
        }
        current = current->next;
      }
    }

    // Now we build the the equalities / disequalities between interface terms
    for (uint32_t i = 0; i < interface_terms.size; i++) {
      for (uint32_t j = i+1; j < interface_terms.size; j++) {
        term_t lhs = interface_terms.data[i];
        term_t rhs = interface_terms.data[j];
        if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Making eq or neq between interface terms ");
          term_print_to_file(out, terms, lhs);
          fprintf(out, " and ");
          term_print_to_file(out, terms, rhs);
          fprintf(out, "\n");
        }

        if (term_bitsize(terms, lhs) == term_bitsize(terms, rhs)) {
          term_t t = (eq_graph_are_equal(&eq_graph, lhs, rhs))? mk_eq(tm, lhs, rhs):mk_neq(tm, lhs, rhs);
          ivector_push(conflict, t);
        }
      }
    }
    delete_ivector(&interface_terms);
  }

  assert(reasons.size == reasons_types.size);
  
  // We collect from the reasons the elements we haven't added
  for (uint32_t i = 0; i < reasons.size; i++) {
      if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Looking at reason %d whose type is %d\n",reasons.data[i],reasons_types.data[i]);
      }
    if (reasons_types.data[i] != REASON_IS_USER) {
      if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Adding to conflict ");
        term_print_to_file(out, terms, reasons.data[i]);
        fprintf(out, "\n");
      }
      ivector_push(conflict, reasons.data[i]);
    }
  }

  // We clean up
  delete_ivector(&reasons_types);
  delete_ivector(&reasons);

  // Destructs egraph
  eq_graph_destruct(&eq_graph);

  // Destructs slicing
  bv_slicing_slicing_destruct(&slicing);

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Returned conflict is: ");
    for (uint32_t i = 0; i < conflict->size; i++) {
      if (i>0) fprintf(out,", ");
      term_print_to_file(out, terms, conflict->data[i]);
    }
    fprintf(out,"\n");
  }

}

/**
 * Normalize the conflict for the following cases
 * - Boolean equalities (must evaluate to true)
 */
void bv_explainer_normalize_conflict(bv_explainer_t* exp, ivector_t* conflict_out) {
  uint32_t i;

  term_table_t* terms = exp->ctx->terms;
  const variable_db_t* var_db = exp->ctx->var_db;
  const mcsat_trail_t* trail = exp->ctx->trail;

  ivector_reset(&exp->tmp_conflict_vec);

  for (i = 0; i < conflict_out->size; ++ i) {
    term_t literal = conflict_out->data[i];
    assert(term_type_kind(terms, literal) == BOOL_TYPE);
    term_kind_t literal_kind = term_kind(terms, literal);

    if (literal_kind == EQ_TERM) {
      term_t literal_pos = unsigned_term(literal);
      variable_t literal_var = variable_db_get_variable_if_exists(var_db, literal_pos);

      // Literal evaluates to true?
      bool evaluates_to_true = literal_var != variable_null &&
          trail_has_value(trail, literal_var) &&
          trail_get_value(trail, literal_var)->b;

      if (evaluates_to_true) {
        // Evaluates to true, good conflict
        ivector_push(&exp->tmp_conflict_vec, literal);
      } else {
        // The individual terms must evaluate to true
        composite_term_t* eq_desc = eq_term_desc(terms, literal_pos);
        term_t lhs = eq_desc->arg[0];
        term_t rhs = eq_desc->arg[1];
        if (is_boolean_term(terms, lhs)) {
          assert(is_boolean_term(terms, rhs));
          // Negate lhs if false
          uint32_t lhs_eval_level = 0;
          const mcsat_value_t* lhs_value = bv_evaluator_evaluate_term(exp->eval, lhs, &lhs_eval_level);
          assert(lhs_value->type == VALUE_BOOLEAN);
          if (!lhs_value->b) {
            lhs = opposite_term(lhs);
          }
          // Negate rhs if false
          uint32_t rhs_eval_level = 0;
          const mcsat_value_t* rhs_value = bv_evaluator_evaluate_term(exp->eval, rhs, &rhs_eval_level);
          assert(rhs_value->type == VALUE_BOOLEAN);
          if (!rhs_value->b) {
            rhs = opposite_term(rhs);
          }
          // Add the literals to the explanations
          ivector_push(&exp->tmp_conflict_vec, lhs);
          ivector_push(&exp->tmp_conflict_vec, rhs);
        } else {
          // Not a Boolean equality, just keep it
          ivector_push(&exp->tmp_conflict_vec, literal);
        }
      }
    } else {
      ivector_push(&exp->tmp_conflict_vec, literal);
    }
  }

  ivector_swap(conflict_out, &exp->tmp_conflict_vec);
  ivector_reset(&exp->tmp_conflict_vec);
}

void bv_explainer_get_conflict(bv_explainer_t* exp, const ivector_t* conflict_in, variable_t conflict_var, ivector_t* conflict_out) {

  bv_subtheory_t subtheory = bv_explainer_get_subtheory(exp, conflict_in);
  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(exp->ctx);
    fprintf(out, "subtheory %s\n", subtheory_to_string(subtheory));
  }

  bool use_yices = false;

  // Get the appropriate conflict
  switch (subtheory) {
  case BV_TH_EQ:
  case BV_TH_EQ_EXT_CON:
    bv_explainer_get_conflict_eq_ext_con(exp, conflict_in, conflict_var, conflict_out);
    break;
  case BV_TH_FULL:
    if (use_yices) {
      bv_explainer_get_conflict_all_with_yices(exp, conflict_in, conflict_var, conflict_out);
    } else {
      bv_explainer_get_conflict_all_simple(exp, conflict_in, conflict_var, conflict_out);
    }
    break;
  default:
    assert(false);
  }

  // Normalize conflict
  bv_explainer_normalize_conflict(exp, conflict_out);
}


