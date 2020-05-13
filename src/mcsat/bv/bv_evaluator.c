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

#include "utils/bit_tricks.h"
#include "mcsat/plugin.h"
#include "mcsat/tracing.h"
#include "mcsat/bv/bv_utils.h"
#include "bv_evaluator.h"

#include <assert.h>

static
void bv_evaluator_run_term(bv_evaluator_t* eval, term_t t, bvconstant_t* out_value, uint32_t* eval_level);

static
bool bv_evaluator_run_atom(bv_evaluator_t* eval, term_t t, uint32_t* eval_level);

void bv_evaluator_construct(bv_evaluator_t* evaluator, const plugin_context_t* ctx) {
  evaluator->ctx = ctx;

  init_pvector(&evaluator->value_cache, 0);
  init_int_hmap(&evaluator->term_values, 0);
  init_int_hmap(&evaluator->atom_values, 0);
  init_int_hmap(&evaluator->level_map, 0);

  mcsat_value_construct_default(&evaluator->eval_value);
}

void bv_evaluator_destruct(bv_evaluator_t* evaluator) {
  uint32_t i;
  for (i = 0; i < evaluator->value_cache.size; ++ i) {
    bvconstant_t* value = evaluator->value_cache.data[i];
    delete_bvconstant(value);
    safe_free(value);
  }
  delete_pvector(&evaluator->value_cache);
  delete_int_hmap(&evaluator->term_values);
  delete_int_hmap(&evaluator->atom_values);
  delete_int_hmap(&evaluator->level_map);

  mcsat_value_destruct(&evaluator->eval_value);
}

void bv_evaluator_clear_cache(bv_evaluator_t* evaluator) {
  for (uint32_t i = 0; i < evaluator->value_cache.size; ++ i) {
    bvconstant_t* value = evaluator->value_cache.data[i];
    delete_bvconstant(value);
    safe_free(value);
  }
  pvector_reset(&evaluator->value_cache);
  int_hmap_reset(&evaluator->term_values);
  int_hmap_reset(&evaluator->atom_values);
  int_hmap_reset(&evaluator->level_map);
}

/** Returns true if in cache */
static inline
bool bv_evaluator_get_atom_cache(bv_evaluator_t* evaluator, term_t t, bool* value, uint32_t* level) {
  assert(is_pos_term(t));
  int_hmap_pair_t* find_level = int_hmap_find(&evaluator->level_map, t);
  if (find_level == NULL) {
    return false;
  } else {
    *level = find_level->val;
    int_hmap_pair_t* find_val = int_hmap_find(&evaluator->atom_values, t);
    assert(find_val != NULL);
    *value = find_val->val;
    return true;
  }
}

/** Returns true if in cache */
static inline
void bv_evaluator_set_atom_cache(bv_evaluator_t* evaluator, term_t t, bool value, uint32_t level) {
  assert(is_pos_term(t));
  assert(int_hmap_find(&evaluator->level_map, t) == NULL);
  assert(int_hmap_find(&evaluator->atom_values, t) == NULL);
  int_hmap_add(&evaluator->level_map, t, level);
  int_hmap_add(&evaluator->atom_values, t, value);
}

/** Returns true if in cache */
static inline
bool bv_evaluator_get_term_cache(bv_evaluator_t* evaluator, term_t t, bvconstant_t* value, uint32_t* level) {
  assert(is_pos_term(t));
  int_hmap_pair_t* find_level = int_hmap_find(&evaluator->level_map, t);
  if (find_level == NULL) {
    return false;
  } else {
    *level = find_level->val;
    int_hmap_pair_t* find_val = int_hmap_find(&evaluator->term_values, t);
    assert(find_val != NULL);
    bvconstant_t* cached_value = evaluator->value_cache.data[find_val->val];
    init_bvconstant(value);
    bvconstant_copy(value, cached_value->bitsize, cached_value->data);
    return true;
  }
}

/** Returns true if in cache */
static inline
void bv_evaluator_set_term_cache(bv_evaluator_t* evaluator, term_t t, bvconstant_t* value, uint32_t level) {
  assert(is_pos_term(t));
  assert(int_hmap_find(&evaluator->level_map, t) == NULL);
  assert(int_hmap_find(&evaluator->term_values, t) == NULL);
  int_hmap_add(&evaluator->level_map, t, level);
  bvconstant_t* value_copy = safe_malloc(sizeof(bvconstant_t));
  init_bvconstant(value_copy);
  bvconstant_copy(value_copy, value->bitsize, value->data);
  int_hmap_add(&evaluator->term_values, t, evaluator->value_cache.size);
  pvector_push(&evaluator->value_cache, value_copy);
}

// Forward declarations

static
void bv_evaluator_run_composite_term(bv_evaluator_t* eval, term_t t, bvconstant_t* out_value, uint32_t* eval_level);

static
void bv_evaluator_run_bv_array(bv_evaluator_t* eval, term_t t, bvconstant_t* out_value, uint32_t* eval_level);

static
void bv_evaluator_run_bv_array(bv_evaluator_t* eval, term_t t, bvconstant_t* out_value, uint32_t* eval_level) {

  term_table_t* terms = eval->ctx->terms;

  assert(term_kind(terms, t) == BV_ARRAY);

  // Term information
  uint32_t t_bitsize = term_bitsize(terms, t);
  composite_term_t* t_composite = composite_term_desc(eval->ctx->terms, t);
  uint32_t t_arity = t_composite->arity;

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Evaluating: ");
    ctx_trace_term(eval->ctx, t);
  }

  // Initialize output
  init_bvconstant(out_value);
  bvconstant_set_bitsize(out_value, t_bitsize);

  // Evaluate all arguments
  for (uint32_t i = 0; i < t_arity; i++) {
    term_t t_i = t_composite->arg[i];
    term_t t_i_pos = unsigned_term(t_i); // Could be Boolean terms, so we negate if needed
    uint32_t eval_level_i = 0;
    bool b_i = bv_evaluator_run_atom(eval, t_i_pos, &eval_level_i);
    if (t_i_pos != t_i) { b_i = !b_i; }
    bvconst_assign_bit(out_value->data, i, b_i);
    if (eval_level_i > *eval_level) { *eval_level = eval_level_i; }
  }

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Term ");
    ctx_trace_term(eval->ctx, t);
    ctx_trace_printf(eval->ctx, " evaluates to ");
    bvconst_print(ctx_trace_out(eval->ctx), out_value->data, out_value->bitsize);
    ctx_trace_printf(eval->ctx, "\n");
  }
}

static
void bv_evaluator_run_composite_term(bv_evaluator_t* eval, term_t t, bvconstant_t* out_value, uint32_t* eval_level) {

  term_table_t* terms = eval->ctx->terms;
  assert(is_bitvector_term(terms, t));

  // Term information
  term_kind_t t_kind = term_kind(terms, t);
  uint32_t t_bitsize = term_bitsize(terms, t);
  composite_term_t* t_composite = composite_term_desc(eval->ctx->terms, t);
  uint32_t t_arity = t_composite->arity;

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Evaluating: ");
    ctx_trace_term(eval->ctx, t);
  }

  // Evaluate all arguments
  bvconstant_t t_arg_val[t_arity];
  for (uint32_t i = 0; i < t_arity; i++) {
    term_t t_i = t_composite->arg[i];
    term_t t_i_pos = unsigned_term(t_i); // Could be Boolean terms, so we negate if needed
    uint32_t eval_level_i = 0;

    bv_evaluator_run_term(eval, t_i_pos, t_arg_val + i, &eval_level_i);
    if (t_i_pos != t_i) {
      bvconst_complement(t_arg_val[i].data, t_arg_val[i].width);
    }
    if (eval_level_i > *eval_level) {
      *eval_level = eval_level_i;
    }
  }

  // Initialize output
  init_bvconstant(out_value);
  bvconstant_set_bitsize(out_value, t_bitsize);

  switch (t_kind) {
  case BV_DIV:
    bvconst_udiv2z(out_value->data, t_arg_val[0].bitsize, t_arg_val[0].data, t_arg_val[1].data);
    break;
  case BV_REM:
    bvconst_urem2z(out_value->data, t_arg_val[0].bitsize, t_arg_val[0].data, t_arg_val[1].data);
    break;
  case BV_SDIV:
    bvconst_sdiv2z(out_value->data, t_arg_val[0].bitsize, t_arg_val[0].data, t_arg_val[1].data);
    break;
  case BV_SREM:
    bvconst_srem2z(out_value->data, t_arg_val[0].bitsize, t_arg_val[0].data, t_arg_val[1].data);
    break;
  case BV_SMOD:
    bvconst_smod2z(out_value->data, t_arg_val[0].bitsize, t_arg_val[0].data, t_arg_val[1].data);
    break;
  case BV_SHL:
    bvconst_lshl(out_value->data, t_arg_val[0].data, t_arg_val[1].data, t_arg_val[0].bitsize);
    break;
  case BV_LSHR:
    bvconst_lshr(out_value->data, t_arg_val[0].data, t_arg_val[1].data, t_arg_val[0].bitsize);
    break;
  case BV_ASHR:
    bvconst_ashr(out_value->data, t_arg_val[0].data, t_arg_val[1].data, t_arg_val[0].bitsize);
    break;
  case BV_ARRAY:
    for (uint32_t i = 0; i < t_arity; ++ i) {
      bool bit_i = bvconst_tst_bit(t_arg_val[i].data, 0);
      bvconst_assign_bit(out_value->data, i, bit_i);
    }
    break;
  default:
    // Not a composite
    assert(false);
    break;
  }

  // Normalize output
  bvconstant_normalize(out_value);

  // Destruct temps
  for (uint32_t i = 0; i < t_arity; i++) {
    delete_bvconstant(t_arg_val + i);
  }

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Term ");
    ctx_trace_term(eval->ctx, t);
    ctx_trace_printf(eval->ctx, " evaluates to ");
    bvconst_print(ctx_trace_out(eval->ctx), out_value->data, out_value->bitsize);
    ctx_trace_printf(eval->ctx, "\n");
  }
}

/**
 * Evaluate term and construct the value into out. User should destruct.
 */
static
void bv_evaluator_run_term(bv_evaluator_t* eval, term_t t, bvconstant_t* out_value, uint32_t* eval_level) {

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Evaluating: ");
    ctx_trace_term(eval->ctx, t);
  }

  assert(is_pos_term(t));

  // Check if cached
  if (bv_evaluator_get_term_cache(eval, t, out_value, eval_level)) {
    return;
  }

  term_table_t* terms = eval->ctx->terms;
  const variable_db_t* var_db = eval->ctx->var_db;
  const mcsat_trail_t* trail = eval->ctx->trail;

  term_kind_t t_kind = term_kind(terms, t);
  switch (t_kind) {
  case CONSTANT_TERM:
    init_bvconstant(out_value);
    bvconstant_set_bitsize(out_value, 1);
    if (t == true_term) {
      bvconst_set_bit(out_value->data, 0);
    } else if (t == false_term) {
      // Nothing
    } else {
      assert(false); // Bool constants only
    }
    break;
  case BV_CONSTANT: {
    bvconst_term_t* t_desc = bvconst_term_desc(terms, t);
    init_bvconstant(out_value);
    bvconstant_set_bitsize(out_value, t_desc->bitsize);
    bvconstant_copy(out_value, t_desc->bitsize, t_desc->data);
    break;
  }
  case BV64_CONSTANT: {
    bvconst64_term_t* t_desc = bvconst64_term_desc(terms, t);
    init_bvconstant(out_value);
    bvconstant_set_bitsize(out_value, t_desc->bitsize);
    bvconstant_copy64(out_value, t_desc->bitsize, t_desc->value);
    break;
  }
  case BV_ARRAY:
    bv_evaluator_run_bv_array(eval, t, out_value, eval_level);
    break;
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
    bv_evaluator_run_composite_term(eval, t, out_value, eval_level);
    break;
  case BIT_TERM: {
    select_term_t* desc = bit_term_desc(terms, t);
    term_t select_arg = desc->arg;
    uint32_t select_idx = desc->idx;
    bvconstant_t select_arg_value;
    bv_evaluator_run_term(eval, select_arg, &select_arg_value, eval_level);
    init_bvconstant(out_value);
    bool select_value = bvconst_tst_bit(select_arg_value.data, select_idx);
    if (select_value) {
      bvconstant_set_all_one(out_value, 1);
    } else {
      bvconstant_set_all_zero(out_value, 1);
    }
    delete_bvconstant(&select_arg_value);
    break;
  }
  case BV_POLY: {
    bvpoly_t* p = bvpoly_term_desc(terms, t);
    init_bvconstant(out_value);
    bvconstant_set_all_zero(out_value, p->bitsize);
    *eval_level = 0;
    for (uint32_t p_i = 0; p_i < p->nterms; ++ p_i) {
      if (p->mono[p_i].var == const_idx) {
        bvconst_add(out_value->data, out_value->width, p->mono[p_i].coeff);
        continue;
      } else {
        term_t t_i = p->mono[p_i].var;
        bvconstant_t t_i_value;
        uint32_t eval_level_i = 0;
        bv_evaluator_run_term(eval, t_i, &t_i_value, &eval_level_i);
        if (eval_level_i > *eval_level) { *eval_level = eval_level_i; }
        bvconst_addmul(out_value->data, out_value->width, p->mono[p_i].coeff, t_i_value.data);
        delete_bvconstant(&t_i_value);
      }
    }
    bvconstant_normalize(out_value);
    break;
  }
  case BV64_POLY: {
    uint64_t sum = 0;
    bvpoly64_t* p = bvpoly64_term_desc(terms, t);
    *eval_level = 0;
    for (uint32_t p_i = 0; p_i < p->nterms; p_i++) {
      if (p->mono[p_i].var == const_idx) {
        sum += p->mono[p_i].coeff;
      } else {
        term_t t_i = p->mono[p_i].var;
        bvconstant_t t_i_value;
        uint32_t eval_level_i = 0;
        bv_evaluator_run_term(eval, t_i, &t_i_value, &eval_level_i);
        if (eval_level_i > *eval_level) { *eval_level = eval_level_i; }
        assert(t_i_value.bitsize <= 64);
        uint64_t t_i_64_value = t_i_value.data[0];
        if (t_i_value.bitsize > 32) {
          t_i_64_value += ((uint64_t) t_i_value.data[1]) << 32;
        }
        sum += p->mono[p_i].coeff * t_i_64_value;
        delete_bvconstant(&t_i_value);
      }
    }
    init_bvconstant(out_value);
    bvconstant_copy64(out_value, p->bitsize, sum);
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* t_pprod = pprod_term_desc(terms, t);
    *eval_level = 0;
    // Start with out_value = 1
    uint32_t bitsize = term_bitsize(terms, t);
    init_bvconstant(out_value);
    bvconstant_set_bitsize(out_value, bitsize);
    bvconst_set_one(out_value->data, out_value->width);
    for (uint32_t i = 0; i < t_pprod->len; ++ i) {
      term_t t_i = t_pprod->prod[i].var;
      uint32_t t_i_exp = t_pprod->prod[i].exp;
      bvconstant_t t_i_value;
      uint32_t eval_level_i = 0;
      bv_evaluator_run_term(eval, t_i, &t_i_value, &eval_level_i);
      if (eval_level_i > *eval_level) { *eval_level = eval_level_i; }
      bvconst_mulpower(out_value->data, out_value->width, t_i_value.data, t_i_exp);
      delete_bvconstant(&t_i_value);
    }
    bvconstant_normalize(out_value);
    break;
  }
  default: { // Variables and foreign terms that are assigned in trail
    // Get the value from trail
    variable_t t_x = variable_db_get_variable_if_exists(var_db, t);
    assert(t_x != variable_null);
    const mcsat_value_t* t_value = trail_get_value(trail, t_x);
    assert(t_value->type == VALUE_BV);
    // Variables and foreign terms
    init_bvconstant(out_value);
    uint32_t t_bitsize = term_bitsize(terms, t);
    bvconstant_copy(out_value, t_bitsize, t_value->bv_value.data);
    // Set the level
    *eval_level = trail_get_level(trail, t_x);
    break;
  }
  }

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Term ");
    ctx_trace_term(eval->ctx, t);
    ctx_trace_printf(eval->ctx, " evaluates to ");
    bvconst_print(ctx_trace_out(eval->ctx), out_value->data, out_value->bitsize);
    ctx_trace_printf(eval->ctx, "\n");
  }

  bv_evaluator_set_term_cache(eval, t, out_value, *eval_level);
 }

static
bool bv_evaluator_run_atom(bv_evaluator_t* eval, term_t t, uint32_t* eval_level) {

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Evaluating: ");
    ctx_trace_term(eval->ctx, t);
  }

  assert(is_pos_term(t));

  // Check if cached
  bool atom_value;
  if (bv_evaluator_get_atom_cache(eval, t, &atom_value, eval_level)) {
    return atom_value;
  }

  term_table_t* terms = eval->ctx->terms;
  term_kind_t t_kind = term_kind(terms, t);

  bool is_variable = false;
  switch (t_kind) {
  case UNINTERPRETED_TERM:
  case ITE_TERM:
  case ITE_SPECIAL:
  case APP_TERM:
    is_variable = true;
    break;
  case EQ_TERM: {
    term_t lhs = eq_term_desc(terms, t)->arg[0];
    if (!is_boolean_term(terms, lhs) && !is_bitvector_term(terms, lhs)) {
      is_variable = true;
    }
    break;
  }
  default:
    is_variable = false;
    break;
  }

  if (is_variable) {
    // Get the value from trail
    variable_t t_x = variable_db_get_variable_if_exists(eval->ctx->var_db, t);
    assert(t_x != variable_null);
    const mcsat_value_t* t_value = trail_get_value(eval->ctx->trail, t_x);
    *eval_level = trail_get_level(eval->ctx->trail, t_x);
    return t_value->b;
  }

  if (t_kind == BIT_TERM) {
    select_term_t* desc = bit_term_desc(terms, t);
    term_t child = desc->arg;
    bvconstant_t value;
    bv_evaluator_run_term(eval, child, &value, eval_level);
    uint32_t bit_index = desc->idx;
    atom_value = bvconst_tst_bit(value.data, bit_index);
    delete_bvconstant(&value);
    bv_evaluator_set_atom_cache(eval, t, atom_value, *eval_level);
    return atom_value;
  }

  if (t_kind == CONSTANT_TERM) {
    assert(t == true_term || t == false_term);
    *eval_level = 0;
    atom_value = (t == true_term);
    bv_evaluator_set_atom_cache(eval, t, atom_value, *eval_level);
    return atom_value;
  }

  if (t_kind == OR_TERM) {
    *eval_level = 0;
    atom_value = false;
    composite_term_t* t_comp = or_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      term_t t_i = t_comp->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      uint32_t level_i = 0;
      bool value_i = bv_evaluator_run_atom(eval, t_i_pos, &level_i);
      if (level_i > *eval_level) { *eval_level = level_i; }
      if (t_i_pos != t_i) { value_i = !value_i; }
      if (value_i) atom_value = true;
    }
    bv_evaluator_set_atom_cache(eval, t, atom_value, *eval_level);
    return atom_value;
  }

  if (t_kind == XOR_TERM) {
    *eval_level = 0;
    atom_value = false;
    composite_term_t* t_comp = xor_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      term_t t_i = t_comp->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      uint32_t level_i = 0;
      bool value_i = bv_evaluator_run_atom(eval, t_i_pos, &level_i);
      if (level_i > *eval_level) { *eval_level = level_i; }
      if (t_i_pos != t_i) { value_i = !value_i; }
      if (value_i) atom_value = !atom_value;
    }
    bv_evaluator_set_atom_cache(eval, t, atom_value, *eval_level);
    return atom_value;
  }

  // Get children value
  composite_term_t* atom_desc = composite_term_desc(terms, t);
  assert(atom_desc->arity == 2);
  term_t t_lhs = atom_desc->arg[0];
  term_t t_rhs = atom_desc->arg[1];

  if (t_kind == EQ_TERM && is_boolean_term(terms, t_lhs)) {
    term_t t_lhs_pos = unsigned_term(t_lhs);
    term_t t_rhs_pos = unsigned_term(t_rhs);
    uint32_t t_lhs_level = 0;
    uint32_t t_rhs_level = 0;
    bool t_value_lhs = bv_evaluator_run_atom(eval, t_lhs_pos, &t_lhs_level);
    bool t_value_rhs = bv_evaluator_run_atom(eval, t_rhs_pos, &t_rhs_level);
    if (t_lhs_level > t_rhs_level) { *eval_level = t_lhs_level; }
    else { *eval_level = t_rhs_level; }
    if (t_lhs_pos != t_lhs) { t_value_lhs = !t_value_lhs; }
    if (t_rhs_pos != t_rhs) { t_value_rhs = !t_value_rhs; }
    atom_value = (t_value_lhs == t_value_rhs);
    bv_evaluator_set_atom_cache(eval, t, atom_value, *eval_level);
    return atom_value;
  }

  bvconstant_t lhs, rhs;
  uint32_t lhs_level = 0, rhs_level = 0;
  bv_evaluator_run_term(eval, t_lhs, &lhs, &lhs_level);
  bv_evaluator_run_term(eval, t_rhs, &rhs, &rhs_level);

  // Output level is max of two levels
  *eval_level = lhs_level > rhs_level ? lhs_level : rhs_level;

  // Compute the actual value
  switch (t_kind) {
  case EQ_TERM: // Boolean equality
  case BV_EQ_ATOM:
    atom_value = bvconst_eq(lhs.data, rhs.data, lhs.width);
    break;
  case BV_GE_ATOM:
    atom_value = bvconst_ge(lhs.data, rhs.data, lhs.bitsize);
    break;
  case BV_SGE_ATOM:
    atom_value = bvconst_sge(lhs.data, rhs.data, lhs.bitsize);
    break;
  default:
    // We're evaluating atoms shouldn't be here
    atom_value = false;
    assert(false);
    break;
  }

  delete_bvconstant(&lhs);
  delete_bvconstant(&rhs);

  if (ctx_trace_enabled(eval->ctx, "mcsat::bv::eval")) {
    ctx_trace_printf(eval->ctx, "Term ");
    ctx_trace_term(eval->ctx, t);
    ctx_trace_printf(eval->ctx, " evaluates to %s", (atom_value ? "true" : "false"));
    ctx_trace_printf(eval->ctx, "\n");
  }

  bv_evaluator_set_atom_cache(eval, t, atom_value, *eval_level);
  return atom_value;
}

const mcsat_value_t* bv_evaluator_evaluate_var(bv_evaluator_t* evaluator, variable_t cstr, uint32_t* cstr_eval_level) {
  const variable_db_t* var_db = evaluator->ctx->var_db;
  term_t cstr_term = variable_db_get_term(var_db, cstr);
  bv_evaluator_clear_cache(evaluator);
  bool result = bv_evaluator_run_atom(evaluator, cstr_term, cstr_eval_level);
  return result ? &mcsat_value_true : &mcsat_value_false;
  bv_evaluator_clear_cache(evaluator);
}

const mcsat_value_t* bv_evaluator_evaluate_term(bv_evaluator_t* evaluator, term_t cstr_term, uint32_t* cstr_eval_level) {
  if (term_type_kind(evaluator->ctx->terms, cstr_term) == BOOL_TYPE) {
    bv_evaluator_clear_cache(evaluator);
    bool negated = is_neg_term(cstr_term);
    cstr_term = unsigned_term(cstr_term);
    bool result = bv_evaluator_run_atom(evaluator, cstr_term, cstr_eval_level);
    if (negated) { result = !result; }
    return result ? &mcsat_value_true : &mcsat_value_false;
  } else {
    bv_evaluator_clear_cache(evaluator);
    bvconstant_t eval_value;
    bv_evaluator_run_term(evaluator, cstr_term, &eval_value, cstr_eval_level);
    mcsat_value_destruct(&evaluator->eval_value);
    mcsat_value_construct_bv_value(&evaluator->eval_value, &eval_value);
    delete_bvconstant(&eval_value);
    return &evaluator->eval_value;
  }
}

void bv_evaluator_csttrail_construct(bv_csttrail_t* csttrail, plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval){
  csttrail->ctx = ctx;
  csttrail->wlm = wlm;
  csttrail->eval = eval;
  csttrail->conflict_var = variable_null;
  csttrail->conflict_var_term = NULL_TERM;
  init_int_hset(&csttrail->free_var, 0);
  init_int_hmap2(&csttrail->fv_cache, 0);
}

// Destruct it
void bv_evaluator_csttrail_destruct(bv_csttrail_t* csttrail){
  delete_int_hset(&csttrail->free_var);
  delete_int_hmap2(&csttrail->fv_cache);
}

// Reset it for dealing with a new conflict
void bv_evaluator_csttrail_reset(bv_csttrail_t* csttrail, variable_t conflict_var, uint32_t optim){
  csttrail->conflict_var = conflict_var;
  csttrail->conflict_var_term = variable_db_get_term(csttrail->ctx->var_db, conflict_var);
  int_hset_reset(&csttrail->free_var);
  csttrail->optim = optim;
}

// Scanning a new atom of the conflict
void bv_evaluator_csttrail_scan(bv_csttrail_t* csttrail, variable_t atom){
  plugin_context_t* ctx = csttrail->ctx;

  variable_list_ref_t list_ref = watch_list_manager_get_list_of(csttrail->wlm, atom);
  variable_t* vars = watch_list_manager_get_list(csttrail->wlm, list_ref);

  for (; *vars != variable_null; vars++) {
    variable_t var = *vars;
    if ((var != atom) && (var != csttrail->conflict_var)) {
      assert(trail_has_value(ctx->trail, var));
      if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Found free variable with value on the trail: ");
        variable_db_print_variable(ctx->var_db, var, out);
        fprintf(out, "\n");
      }
      int_hset_add(&csttrail->free_var, var);
    }
  }
}

uint32_t bv_evaluator_not_free_up_to(bv_csttrail_t* csttrail, term_t u) {

  plugin_context_t* ctx = csttrail->ctx;
  term_manager_t* tm    = ctx->tm;
  variable_db_t* var_db = ctx->var_db; // standard abbreviations
  term_table_t* terms   = ctx->terms;
  term_t t              = unsigned_term(bv_bitterm(terms,u));
  term_t y              = csttrail->conflict_var_term;

  if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_evaluator (optim=%d) looks at how many bits do not refer to variable y = ",csttrail->optim);
    term_print_to_file(out, ctx->terms, y);
    fprintf(out, " in term ");
    ctx_trace_term(ctx, u);
  }

  assert(t != NULL_TERM);
  assert(is_bitvector_term(terms, t) || is_boolean_term(terms, t));

  if (t == y) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "This term is y!\n");
    }
    return 0; // It doesn't feature y up to bit 0
  }
  switch (term_kind(terms, t)) { // Simple check for constants
  case CONSTANT_TERM:
  case BV_CONSTANT:
  case BV64_CONSTANT: {
    if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "This term is a constant!\n");
    }
    return -1; // no variables at all
  }
  default: {
  }
  }

  // Is t a variable different than y?
  uint32_t w     = bv_term_bitsize(terms, t);
  variable_t var = variable_db_get_variable_if_exists(var_db, t); // term as a variable

  // If ((var != variable_null) && int_hset_member(&csttrail->free_var, var))
  // then t is another variable than y; it has variables and we don't look into its structure.
  if (var != variable_null
      && int_hset_member(&csttrail->free_var, var)) { // t is a variable other than y
    if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "This term is a free variable of the conflict with a value on the trail: ");
      ctx_trace_term(ctx, t);
    }
    return w;
  }

  // Now we look into whether the answer is memoised
  int_hmap2_rec_t* registered;

  // The next commented code is for when we decide to scan the term for its free variables,
  // registering its top var and bottom var in -1 and -2 cell, respectively
  /* registered = int_hmap2_find(&csttrail->fv_cache, t, -1); // Get top var of t */
  /* if (registered != NULL && registered->val < y) { // Do we know its top variable and is it < y ? */
  /*   if (registered->val == 0) // The term has no variables at all (maybe doesn't happen in yices) */
  /*     return -1; */
  /*   registered = int_hmap2_find(&csttrail->fv_cache, t, NULL_TERM); */
  /*   assert(registered != NULL); */
  /*   return registered->val; */
  /* } */
  /* registered = int_hmap2_find(&csttrail->fv_cache, t, -2); // Get bottom var of t */
  /* if (registered != NULL && registered->val > y) { // Do we know its bottom variable and is it > y ? */
  /*   registered = int_hmap2_find(&csttrail->fv_cache, t, NULL_TERM); */
  /*   assert(registered != NULL); */
  /*   return registered->val; */
  /* } */
  registered = int_hmap2_find(&csttrail->fv_cache, t, (3*y) + csttrail->optim);
  if (registered != NULL) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "This term has previously been found to not use y up to bit %d ",registered->val);
      ctx_trace_term(ctx, t);
    }
    return registered->val; // Returning memoised value
  }
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Looking at the kind of ");
    ctx_trace_term(ctx, t);
  }

  uint32_t result = w;

  switch (term_kind(terms, t)) {
  case CONSTANT_TERM:
  case BV_CONSTANT:
  case BV64_CONSTANT:
    assert(false); // Already treated above
    break;
  case EQ_TERM:
  case OR_TERM:
  case XOR_TERM:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR: {
    composite_term_t* composite_desc = composite_term_desc(terms, t);
    for (uint32_t i = 0; i < composite_desc->arity; ++ i) {
      term_t t_i = composite_desc->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      if (bv_evaluator_not_free_up_to(csttrail, t_i_pos)
          < bv_term_bitsize(tm->terms, t_i_pos)) {
        result = 0;
        break;
      }
    }
    break;
  }
  case BIT_TERM: {
    term_t arg = bit_term_arg(terms, t);
    uint32_t index = bit_term_index(terms, t);
    term_t arg_pos = unsigned_term(arg);
    if (csttrail->optim == 0
        && bv_evaluator_not_free_up_to(csttrail, arg_pos) < bv_term_bitsize(tm->terms, arg_pos))
      result = 0;
    else
      result = (index < bv_evaluator_not_free_up_to(csttrail, arg_pos)) ? 1 : 0;
    break;
  }
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      uint32_t recurs = bv_evaluator_not_free_up_to(csttrail, t_poly->mono[i].var);
      if (csttrail->optim == 2) {
        uint32_t shift = (uint32_t) bvconst_ctz(t_poly->mono[i].coeff, t_poly->width);
        if (shift > 0) recurs = (recurs+shift < w) ? (recurs+shift) : w;
      }
      if (recurs < result)
        result = (csttrail->optim == 2) ? recurs : 0;
      if (result == 0) break;
    }
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      uint32_t recurs = bv_evaluator_not_free_up_to(csttrail, t_poly->mono[i].var);
      if (csttrail->optim == 2) {
        uint32_t shift = ctz64(t_poly->mono[i].coeff);
        if (shift > 0) recurs = (recurs+shift < w) ? (recurs+shift) : w;
      }
      if (recurs < result)
        result = (csttrail->optim == 2) ? recurs : 0;
      if (result == 0) break;
    }
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* t_pprod = pprod_term_desc(terms, t);
    for (uint32_t i = 0; i < t_pprod->len; ++ i) {
      uint32_t recurs = bv_evaluator_not_free_up_to(csttrail, t_pprod->prod[i].var);
      if (recurs < result)
        result = (csttrail->optim == 2) ? recurs : 0;
      if (result == 0) break;
    }
    break;
  }
  case BV_ARRAY: {
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    result = 0;
    for (uint32_t i = 0; i < w; i++) {
      term_t t_i = concat_desc->arg[i];
      t_i = unsigned_term(t_i);
      if (bv_evaluator_not_free_up_to(csttrail, t_i) == 0)
        break;
      result++;
    }
    if (csttrail->optim == 0 && result < w)
      result = 0;
    break;
  }
  default:
    result = 0;
  }

  int_hmap2_add(&csttrail->fv_cache, t, (3*y) + csttrail->optim, result);
  if (ctx_trace_enabled(ctx, "mcsat::bv::scan")) {
    FILE* out = ctx_trace_out(ctx);
    ctx_trace_term(ctx, t);
    fprintf(out, "...does not have y among first %d bits\n",result);
  }

  return result;
  
}

// Checks whether term t evaluates, all its BV-variables having values on the trail.
// If it does not, use_trail is untouched. If it does, then use_trail is set to true
// if the trail is actually used (i.e. term has a BV-variable), otherwise it is set to false.

bool bv_evaluator_is_evaluable(bv_csttrail_t* csttrail, term_t u) {
  uint32_t result = bv_evaluator_not_free_up_to(csttrail, u);
  return (result >= bv_term_bitsize(csttrail->ctx->terms, u));
}

