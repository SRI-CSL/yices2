/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "bv_explainer.h"
#include "mcsat/variable_db.h"
#include "mcsat/tracing.h"
#include "mcsat/utils/int_mset.h"

#include <inttypes.h>

static
const char* subtheory_to_string(bv_subtheory_t th) {
  switch (th) {
    case BV_TH_EQ: return "equality";
    case BV_TH_EQ_EXT_CON: return "extract/concat";
    case BV_TH_BITWISE: return "bitwise";
    case BV_TH_SHIFT: return "shifts";
    case BV_TH_ARITH_CMP: return "compare";
    case BV_TH_ARITH: return "arithmetic";
    case BV_TH_FULL: return "full";
    default:
      assert(false);
  }
  return "unknown";
}

void bv_explainer_construct(bv_explainer_t* exp, const plugin_context_t* ctx, watch_list_manager_t* wlm) {
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
void bv_explainer_get_subtheories(bv_explainer_t* exp, term_t t, int* subtheory_count) {

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
    if (t0 != t0_pos) subtheory_count[BV_TH_BITWISE] ++;
    term_t t1 = atom_comp->arg[1], t1_pos = unsigned_term(t1);
    if (t1 != t1_pos) subtheory_count[BV_TH_BITWISE] ++;
    bv_explainer_get_subtheories(exp, t0_pos, subtheory_count);
    bv_explainer_get_subtheories(exp, t1_pos, subtheory_count);
    subtheory_count[BV_TH_EQ] ++;
    break;
  }
  case BV_EQ_ATOM: {
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    bv_explainer_get_subtheories(exp, atom_comp->arg[0], subtheory_count);
    bv_explainer_get_subtheories(exp, atom_comp->arg[1], subtheory_count);
    subtheory_count[BV_TH_EQ] ++;
    break;
  }
  case BV_GE_ATOM:
  case BV_SGE_ATOM: {
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    bv_explainer_get_subtheories(exp, atom_comp->arg[0], subtheory_count);
    bv_explainer_get_subtheories(exp, atom_comp->arg[1], subtheory_count);
    subtheory_count[BV_TH_ARITH_CMP] ++;
    break;
  }
  case BV_ARRAY: {
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    for (uint32_t i = 0; i < concat_desc->arity; ++ i) {
      term_t t_i = concat_desc->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      if (t_i != t_i_pos) subtheory_count[BV_TH_BITWISE] ++;
      bv_explainer_get_subtheories(exp, t_i_pos, subtheory_count);
    }
    subtheory_count[BV_TH_EQ_EXT_CON] ++;
    break;
  }
  case OR_TERM: {
    composite_term_t* t_comp = or_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      term_t t_i = t_comp->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      bv_explainer_get_subtheories(exp, t_i_pos, subtheory_count);
    }
    subtheory_count[BV_TH_BITWISE] ++;
    break;
  }
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:{
    composite_term_t* t_comp = composite_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      bv_explainer_get_subtheories(exp, t_comp->arg[i], subtheory_count);
    }
    subtheory_count[BV_TH_ARITH] ++;
    break;
  }
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR: {
    composite_term_t* t_comp = composite_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      bv_explainer_get_subtheories(exp, t_comp->arg[i], subtheory_count);
    }
    subtheory_count[BV_TH_SHIFT] ++;
    break;
  }
  case BIT_TERM:
    bv_explainer_get_subtheories(exp, bit_term_arg(terms, t), subtheory_count);
    subtheory_count[BV_TH_EQ_EXT_CON] ++;
    break;
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_explainer_get_subtheories(exp, t_poly->mono[i].var, subtheory_count);
    }
    subtheory_count[BV_TH_ARITH] ++;
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_explainer_get_subtheories(exp, t_poly->mono[i].var, subtheory_count);
    }
    subtheory_count[BV_TH_ARITH] ++;
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* t_pprod = pprod_term_desc(terms, t);
    for (uint32_t i = 0; i < t_pprod->len; ++ i) {
      bv_explainer_get_subtheories(exp, t_pprod->prod[i].var, subtheory_count);
    }
    subtheory_count[BV_TH_ARITH] ++;
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
  int theory_count[BV_TH_COUNT];
  for (i = 0; i < conflict->size; i ++) {
    term_t t = variable_db_get_term(var_db, conflict->data[i]);
    bv_explainer_get_subtheories(exp, t, theory_count);
  }

  if (ctx_trace_enabled(exp->ctx, "mcsat::bv::conflict")) {
    bv_subtheory_t th;
    FILE* out = ctx_trace_out(exp->ctx);
    fprintf(out, "subtheories:\n");
    for (th = 0; th < BV_TH_COUNT; ++ th) {
      if (theory_count[th] > 0) {
        fprintf(out, "%s\n", subtheory_to_string(th));
      }
    }
  }

  return BV_TH_FULL;
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

  switch (subtheory) {
  case BV_TH_EQ:
    assert(false);
    break;
  case BV_TH_EQ_EXT_CON:
    assert(false);
    break;
  case BV_TH_FULL:
    bv_explainer_get_conflict_all(exp, conflict_in, conflict_var, conflict_out);
    break;
  default:
    assert(false);
  }
}


