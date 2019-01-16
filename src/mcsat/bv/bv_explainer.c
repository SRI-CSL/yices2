/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "bv_slicing.h"
#include "bv_explainer.h"
#include "mcsat/variable_db.h"
#include "mcsat/tracing.h"
#include "mcsat/utils/int_mset.h"
#include "mcsat/eq/equality_graph.h"

#include <inttypes.h>

static
const char* bv_kind_to_string(bv_kind_type_t kt) {
  switch (kt) {
  case BV_KIND_EQ: return "equality";
  case BV_KIND_EXT_CON: return "extract/concat";
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
    0, // BV_KIND_BITWISE,
    0, // BV_KIND_SHIFT,
    0, // BV_KIND_ARITH_CMP,
    0, // BV_KIND_ARITH_POLY
};

int bv_th_eq_ext_con[BV_KIND_COUNT] = {
    1, // BV_KIND_EQ = 0,
    1, // BV_KIND_EXT_CON,
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

void bv_explainer_construct(bv_explainer_t* exp, plugin_context_t* ctx, watch_list_manager_t* wlm) {
  exp->ctx = ctx;
  exp->tm = &ctx->var_db->tm;
  exp->wlm = wlm;

  init_int_hset(&exp->visited_cache, 0);

  exp->stats.th_eq = statistics_new_int(exp->ctx->stats, "mcsat::bv::conflicts_eq");
  exp->stats.th_eq_ext_con = statistics_new_int(exp->ctx->stats, "mcsat::bv::conflict_eq_ext_con");
  exp->stats.th_full = statistics_new_int(exp->ctx->stats, "mcsat::bv::conflicts_full");
}

void bv_explainer_destruct(bv_explainer_t* exp) {
  delete_int_hset(&exp->visited_cache);
}

static
void bv_explainer_count_subtheories(bv_explainer_t* exp, term_t t, int* kinds_count) {

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
    bv_explainer_count_subtheories(exp, t0_pos, kinds_count);
    bv_explainer_count_subtheories(exp, t1_pos, kinds_count);
    kinds_count[BV_KIND_EQ] ++;
    break;
  }
  case BV_EQ_ATOM: {
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    bv_explainer_count_subtheories(exp, atom_comp->arg[0], kinds_count);
    bv_explainer_count_subtheories(exp, atom_comp->arg[1], kinds_count);
    kinds_count[BV_KIND_EQ] ++;
    break;
  }
  case BV_GE_ATOM:
  case BV_SGE_ATOM: {
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    bv_explainer_count_subtheories(exp, atom_comp->arg[0], kinds_count);
    bv_explainer_count_subtheories(exp, atom_comp->arg[1], kinds_count);
    kinds_count[BV_KIND_ARITH_CMP] ++;
    break;
  }
  case BV_ARRAY: {
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    for (uint32_t i = 0; i < concat_desc->arity; ++ i) {
      term_t t_i = concat_desc->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      if (t_i != t_i_pos) kinds_count[BV_KIND_BITWISE] ++;
      bv_explainer_count_subtheories(exp, t_i_pos, kinds_count);
    }
    kinds_count[BV_TH_EQ_EXT_CON] ++;
    break;
  }
  case OR_TERM: {
    composite_term_t* t_comp = or_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      term_t t_i = t_comp->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      bv_explainer_count_subtheories(exp, t_i_pos, kinds_count);
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
      bv_explainer_count_subtheories(exp, t_comp->arg[i], kinds_count);
    }
    kinds_count[BV_KIND_ARITH_POLY] ++;
    break;
  }
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR: {
    composite_term_t* t_comp = composite_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      bv_explainer_count_subtheories(exp, t_comp->arg[i], kinds_count);
    }
    kinds_count[BV_KIND_SHIFT] ++;
    break;
  }
  case BIT_TERM:
    bv_explainer_count_subtheories(exp, bit_term_arg(terms, t), kinds_count);
    kinds_count[BV_KIND_EXT_CON] ++;
    break;
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_explainer_count_subtheories(exp, t_poly->mono[i].var, kinds_count);
    }
    kinds_count[BV_KIND_ARITH_POLY] ++;
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_explainer_count_subtheories(exp, t_poly->mono[i].var, kinds_count);
    }
    kinds_count[BV_KIND_ARITH_POLY] ++;
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* t_pprod = pprod_term_desc(terms, t);
    for (uint32_t i = 0; i < t_pprod->len; ++ i) {
      bv_explainer_count_subtheories(exp, t_pprod->prod[i].var, kinds_count);
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
    bv_explainer_count_subtheories(exp, t, kind_count);
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

static
void bv_explainer_get_conflict_eq(bv_explainer_t* exp, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {

  uint32_t i;
  variable_t atom_i_var;
  term_t atom_i_term;

  exp->stats.th_eq ++;

  term_table_t* terms = exp->ctx->terms;
  const variable_db_t* var_db = exp->ctx->var_db;

  // Create the equality graph
  eq_graph_t eq_graph;
  eq_graph_construct(&eq_graph, exp->ctx, "bv:eq");

  // Add all terms to the equality graph
  for (i = 0; i < conflict_core->size; ++ i) {
    atom_i_var = conflict_core->data[i];
    atom_i_term = variable_db_get_term(var_db, atom_i_var);
    // Add the LHS/RHS
    term_kind_t atom_kind = term_kind(terms, atom_i_term);
    composite_term_t* atom_i_desc;
    switch(atom_kind) {
    case EQ_TERM:
      atom_i_desc = eq_term_desc(terms, atom_i_term);
      eq_graph_add_ifun_term(&eq_graph, atom_i_term, EQ_TERM, 2, atom_i_desc->arg);
      break;
    case BV_EQ_ATOM:
      atom_i_desc = bveq_atom_desc(terms, atom_i_term);
      eq_graph_add_ifun_term(&eq_graph, atom_i_term, EQ_TERM, 2, atom_i_desc->arg);
      break;
    default:
      assert(false);
    }
  }

  // Run propagation (TODO: run just for the conflict terms)
  eq_graph_propagate_trail(&eq_graph);

  // Conflict might be due to not enough
  if (!eq_graph.in_conflict) {
    if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
      FILE* out = ctx_trace_out(exp->ctx);
      eq_graph_print(&eq_graph, out);
    }
    assert(false);
  }

  // Construct the conflict
  eq_graph_get_conflict(&eq_graph, conflict, NULL, NULL);

  // Delete temps
  eq_graph_destruct(&eq_graph);
}


static
void bv_explainer_get_conflict_eq_ext_con(bv_explainer_t* exp, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {

  exp->stats.th_eq_ext_con ++;

  plugin_context_t* ctx = exp->ctx;
  /* const term_table_t* terms   = ctx->terms; */
  /* const variable_db_t* var_db = ctx->var_db; */

  // Do the slicing
  slicing_t slicing;
  bv_slicing(ctx, conflict_core, conflict_var, &slicing);

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::slicing")) {
    FILE* out = ctx_trace_out(exp->ctx);
    bv_slicing_print_slicing(ctx->var_db, &slicing, out);
  }

  // Create the equality graph
  eq_graph_t eq_graph;
  eq_graph_construct(&eq_graph, exp->ctx, "bv:eq");

  
  // TODO: SMT'2017 paper

  // Delete temps
  eq_graph_destruct(&eq_graph);
  bv_slicing_slicing_destruct(&slicing);
  
}

static
void bv_explainer_get_conflict_all(bv_explainer_t* exp, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {
  uint32_t i;
  variable_t atom_i_var;
  term_t atom_i_term;
  bool atom_i_value;

  const variable_db_t* var_db = exp->ctx->var_db;
  const mcsat_trail_t* trail = exp->ctx->trail;

  exp->stats.th_full ++;

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

void bv_explainer_get_conflict(bv_explainer_t* exp, const ivector_t* conflict_in, variable_t conflict_var, ivector_t* conflict_out) {

  bv_subtheory_t subtheory = bv_explainer_get_subtheory(exp, conflict_in);
  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(exp->ctx);
    fprintf(out, "subtheory %s\n", subtheory_to_string(subtheory));
  }

  switch (subtheory) {
  case BV_TH_EQ:
    bv_explainer_get_conflict_eq(exp, conflict_in, conflict_var, conflict_out);
    break;
  case BV_TH_EQ_EXT_CON:
    bv_explainer_get_conflict_eq_ext_con(exp, conflict_in, conflict_var, conflict_out);
    break;
  case BV_TH_FULL:
    bv_explainer_get_conflict_all(exp, conflict_in, conflict_var, conflict_out);
    break;
  default:
    assert(false);
  }
}


