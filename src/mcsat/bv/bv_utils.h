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

#pragma once

/*
 * BD: this is needed to build in debug mode on cygwin/windows
 */
#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdio.h>

#include "utils/hash_functions.h"
#include "terms/terms.h"
#include "terms/term_manager.h"
#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "yices.h"
#include "api/yices_api_lock_free.h"

/** Types of bitvector terms */
typedef enum {
  /** Constants */
  BV_TERM_CONSTANT,
  /** Composite terms (including negation) */
  BV_TERM_COMPOSITE,
  /** Selection of a single bit */
  BV_TERM_BITSELECT,
  /** A bitvector polynomial */
  BV_TERM_POLY,
  /** Everything else we consider a variable */
  BV_TERM_VARIABLE
} bv_term_type_t;

/**
 * Bitsize of terms. We consider Boolean terms to be bit-vector terms of size 1.
 */
static inline
uint32_t bv_term_bitsize(const term_table_t* terms, term_t t) {
  type_kind_t t_type = term_type_kind(terms, t);
  assert(t_type == BOOL_TYPE || t_type == BITVECTOR_TYPE);
  if (t_type == BOOL_TYPE) {
    return 1;
  } else {
    return term_bitsize(terms, t);
  }
}

/** Whether the bitvector term has any children (including negation) */
static inline
bool bv_term_has_children(term_table_t* terms, term_t t) {
  if (is_neg_term(t)) {
    return true;
  } else {
    term_kind_t kind = term_kind(terms, t);
    switch (kind) {
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case EQ_TERM: // Boolean
    case OR_TERM: // Boolean
    case XOR_TERM: // Boolean
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    case BIT_TERM:
    case BV_POLY:
    case BV64_POLY:
    case POWER_PRODUCT:
      return true;
    default:
      return false;
    }
  }
}

/** Get the bitvector type of the term type */
static inline
bv_term_type_t bv_term_kind_get_type(term_kind_t kind) {
  switch (kind) {
  case CONSTANT_TERM:
  case BV_CONSTANT:
  case BV64_CONSTANT:
    return BV_TERM_CONSTANT;
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case EQ_TERM:
  case OR_TERM:
  case XOR_TERM:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
    return BV_TERM_COMPOSITE;
  case BIT_TERM:
    return BV_TERM_BITSELECT;
  case BV_POLY:
  case BV64_POLY:
  case POWER_PRODUCT:
    return BV_TERM_POLY;
  default:
    return BV_TERM_VARIABLE;
  }
}

static inline bv_term_type_t bv_term_get_type(term_table_t* terms, term_t t) {
  if (is_neg_term(t)) {
    return BV_TERM_COMPOSITE;
  } else {
    term_kind_t kind = term_kind(terms, t);
    if (kind == EQ_TERM) {
      composite_term_t* eq = eq_term_desc(terms, t);
      if (!is_boolean_term(terms, eq->arg[0]) && !is_bitvector_term(terms, eq->arg[0])) {
        return BV_TERM_VARIABLE;
      }
    }
    return bv_term_kind_get_type(kind);
  }
}

/**
 * Do we treat this term as a bit-vector variable:
 * a) if it's a bit-vector variable
 * b) if it's a term of type bit-vector but foreign (e.g., f(x))
 * c) if it's a Boolean term (bit-vector size 1)
 */
static inline
bool bv_term_is_variable(term_table_t* terms, term_t t) {
  if (bv_term_get_type(terms, t) == BV_TERM_VARIABLE)
    return true;
  if (term_kind(terms, t) == EQ_TERM) {
    composite_term_t* eq = eq_term_desc(terms, t);
    if (!is_boolean_term(terms, eq->arg[0]) && !is_bitvector_term(terms, eq->arg[0])) {
      return true;
    }
  }
  return false;
}

/**
 * Compute the value of a term, given the value of all the children. Only works
 * for composite terms (i.e.. terms that have children).
 */
static inline
void bv_term_compute_value(term_table_t* terms, term_t t, bvconstant_t** children_values, bvconstant_t* out_value) {
  assert(bv_term_has_children(terms, t));

  if (is_neg_term(t)) {
    if (bvconst_tst_bit(children_values[0]->data, 0)) {
      bvconst_clr_bit(out_value->data, 0);
    } else {
      bvconst_set_bit(out_value->data, 0);
    }
  } else {
    term_kind_t kind = term_kind(terms, t);
    uint32_t bitsize = bv_term_bitsize(terms, t);
    switch (kind) {
    case EQ_TERM:
    case BV_EQ_ATOM: {
      uint32_t k = children_values[0]->width;
      bool values_eq = bvconst_eq(children_values[0]->data, children_values[1]->data, k);
      if (values_eq) {
        bvconst_set_bit(out_value->data, 0);
      } else {
        bvconst_clr_bit(out_value->data, 0);
      }
      break;
    }
    case BV_GE_ATOM: {
      bool values_ge = bvconst_ge(children_values[0]->data, children_values[1]->data, children_values[0]->bitsize);
      if (values_ge) {
        bvconst_set_bit(out_value->data, 0);
      } else {
        bvconst_clr_bit(out_value->data, 0);
      }
      break;
    }
    case BV_SGE_ATOM: {
      bool values_sge = bvconst_sge(children_values[0]->data, children_values[1]->data, children_values[0]->bitsize);
      if (values_sge) {
        bvconst_set_bit(out_value->data, 0);
      } else {
        bvconst_clr_bit(out_value->data, 0);
      }
      break;
    }
    case BV_DIV:
      bvconst_udiv2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      bvconst_normalize(out_value->data, bitsize);
      break;
    case BV_REM:
      bvconst_urem2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      bvconst_normalize(out_value->data, bitsize);
      break;
    case BV_SDIV:
      bvconst_sdiv2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      bvconst_normalize(out_value->data, bitsize);
      break;
    case BV_SREM:
      bvconst_srem2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      bvconst_normalize(out_value->data, bitsize);
      break;
    case BV_SMOD:
      bvconst_smod2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      bvconst_normalize(out_value->data, bitsize);
      break;
    case BV_SHL:
      bvconst_lshl(out_value->data, children_values[0]->data, children_values[1]->data, bitsize);
      break;
    case BV_LSHR:
      bvconst_lshr(out_value->data, children_values[0]->data, children_values[1]->data, bitsize);
      break;
    case BV_ASHR:
      bvconst_ashr(out_value->data, children_values[0]->data, children_values[1]->data, bitsize);
      break;
    case BV_ARRAY: {
      composite_term_t* t_composite = composite_term_desc(terms, t);
      uint32_t t_arity = t_composite->arity;
      for (uint32_t i = 0; i < t_arity; ++ i) {
        bool bit_i = bvconst_tst_bit(children_values[i]->data, 0);
        bvconst_assign_bit(out_value->data, i, bit_i);
      }
      break;
    }
    case OR_TERM: {
      composite_term_t* t_composite = or_term_desc(terms, t);
      uint32_t t_arity = t_composite->arity;
      bvconst_clr_bit(out_value->data, 0);
      for (uint32_t i = 0; i < t_arity; ++i) {
        bool bit_i = bvconst_tst_bit(children_values[i]->data, 0);
        if (bit_i) {
          bvconst_set_bit(out_value->data, 0);
          break;
        }
      }
      break;
    }
    case XOR_TERM: {
      composite_term_t* t_composite = xor_term_desc(terms, t);
      uint32_t t_arity = t_composite->arity;
      bvconst_clr_bit(out_value->data, 0);
      for (uint32_t i = 0; i < t_arity; ++i) {
        bool bit_i = bvconst_tst_bit(children_values[i]->data, 0);
        if (bit_i) {
          bvconst_flip_bit(out_value->data, 0);
        }
      }
      break;
    }
    case BIT_TERM: {
      select_term_t* desc = bit_term_desc(terms, t);
      uint32_t select_idx = desc->idx;
      bool select_value = bvconst_tst_bit(children_values[0]->data, select_idx);
      if (select_value) {
        bvconst_set_bit(out_value->data, 0);
      } else {
        bvconst_clr_bit(out_value->data, 0);
      }
      break;
    }
    case BV_POLY: {
      bvpoly_t* p = bvpoly_term_desc(terms, t);
      bvconstant_set_all_zero(out_value, bitsize);
      for (uint32_t p_i = 0, child_i = 0; p_i < p->nterms; ++ p_i) {
        if (p->mono[p_i].var == const_idx) {
          bvconst_add(out_value->data, out_value->width, p->mono[p_i].coeff);
        } else {
          bvconstant_t* t_i_value = (bvconstant_t*) children_values[child_i ++];
          bvconst_addmul(out_value->data, out_value->width, p->mono[p_i].coeff, t_i_value->data);
        }
      }
      bvconstant_normalize(out_value);
      break;
    }
    case BV64_POLY: {
      uint64_t sum = 0;
      bvpoly64_t* p = bvpoly64_term_desc(terms, t);
      for (uint32_t p_i = 0, child_i = 0; p_i < p->nterms; p_i++) {
        if (p->mono[p_i].var == const_idx) {
          sum += p->mono[p_i].coeff;
        } else {
          bvconstant_t* t_i_value = (bvconstant_t*) children_values[child_i ++];
          uint64_t t_i_64_value = t_i_value->data[0];
          if (t_i_value->bitsize > 32) {
            t_i_64_value += ((uint64_t) t_i_value->data[1]) << 32;
          }
          sum += p->mono[p_i].coeff * t_i_64_value;
        }
      }
      bvconstant_copy64(out_value, p->bitsize, sum);
      break;
    }
    case POWER_PRODUCT: {
      pprod_t* t_pprod = pprod_term_desc(terms, t);
      // Start with out_value = 1
      bvconstant_set_bitsize(out_value, bitsize);
      bvconst_set_one(out_value->data, out_value->width);
      for (uint32_t i = 0; i < t_pprod->len; ++ i) {
        uint32_t t_i_exp = t_pprod->prod[i].exp;
        bvconstant_t* t_i_value = (bvconstant_t*) children_values[i];
        bvconst_mulpower(out_value->data, out_value->width, t_i_value->data, t_i_exp);
      }
      bvconstant_normalize(out_value);
      break;
    }
    default:
      // Not composite
      assert(false);
      break;
    }
  }
}

/** Construct a composite bitvector term (including some Boolean terms) */
static inline
term_t mk_bv_composite(term_manager_t* tm, term_kind_t kind, uint32_t n, term_t* children) {

  switch (kind) {
  case EQ_TERM:            // equality
    assert(n == 2);
    return mk_eq(tm, children[0], children[1]);
  case OR_TERM:            // n-ary OR
    assert(n > 1);
    return mk_or(tm, n, children);
  case XOR_TERM:           // n-ary XOR
    return mk_xor(tm, n, children);
  case BV_ARRAY:
    assert(n >= 1);
    return mk_bvarray(tm, n, children);
  case BV_DIV:
    assert(n == 2);
    return mk_bvdiv(tm, children[0], children[1]);
  case BV_REM:
    assert(n == 2);
    return mk_bvrem(tm, children[0], children[1]);
  case BV_SDIV:
    assert(n == 2);
    return mk_bvsdiv(tm, children[0], children[1]);
  case BV_SREM:
    assert(n == 2);
    return mk_bvsrem(tm, children[0], children[1]);
  case BV_SMOD:
    assert(n == 2);
    return mk_bvsmod(tm, children[0], children[1]);
  case BV_SHL:
    assert(n == 2);
    return mk_bvshl(tm, children[0], children[1]);
  case BV_LSHR:
    assert(n == 2);
    return mk_bvlshr(tm, children[0], children[1]);
  case BV_ASHR:
    assert(n == 2);
    return mk_bvashr(tm, children[0], children[1]);
  case BV_EQ_ATOM:
    assert(n == 2);
    return mk_bveq(tm, children[0], children[1]);
  case BV_GE_ATOM:
    assert(n == 2);
    return mk_bvge(tm, children[0], children[1]);
  case BV_SGE_ATOM:
    assert(n == 2);
    return mk_bvsge(tm, children[0], children[1]);
  case ITE_TERM: {
    assert(n == 3);
    type_t tau = term_type(tm->terms, children[1]);
    return mk_ite(tm, children[0], children[1], children[2], tau);
  }
  default:
    assert(false);
    return NULL_TERM;
  }
}

// builds extracted term, form lo (inc.) to hi (exc.)
// can be given a Boolean term, in which case it returns a bitvector of size 1
static inline
term_t term_extract(term_manager_t* tm, term_t t, uint32_t lo, uint32_t hi) {
  assert(is_bitvector_term(tm->terms, t) || is_boolean_term(tm->terms, t));
  if (is_bitvector_term(tm->terms, t)
      && lo == 0
      && hi == term_bitsize(tm->terms, t))
    return t;
  term_t tarray[1];
  tarray[0] = t;
  bvlogic_buffer_t* buffer = term_manager_get_bvlogic_buffer(tm);
  term_t bv_term = is_bitvector_term(tm->terms, t) ?
    t : bvarray_term(tm->terms, 1, tarray);
  bvlogic_buffer_set_slice_term(buffer, tm->terms, lo, hi-1, bv_term);
  return mk_bvlogic_term(tm, buffer);
}

// Gets the bit term by descending the BIT_TERM-over-BV_ARRAY situations
static inline
term_t bv_bitterm(term_table_t* terms, term_t t) {
  term_t result = t;
  bool is_pos = true; // Parity of how many negations have we seen in the descent
  while (term_kind(terms, result) == BIT_TERM
         && term_kind(terms, bit_term_arg(terms, result)) == BV_ARRAY) {
    if (!is_pos_term(result)) is_pos = !is_pos;
    uint32_t index = bit_term_index(terms, result);  // Get selected bit
    term_t base    = bit_term_arg(terms, result);    // Get the base
    composite_term_t* concat_desc = bvarray_term_desc(terms, base);
    result = concat_desc->arg[index];
  }
  return is_pos ? result : not_term(terms, result);
}

// The following 2 functions are for the implementation of a very lightweight hashtable of terms
// with fixed size. Table is supposed to contain few entries. Can't remove entries.

static inline
void fix_htbl_init(term_t* htbl, uint32_t size){
  for (uint32_t i = 0; i < size; i++)
    htbl[i] = NULL_TERM;
}

// Gives back the index of a cell for a given term.
// size is the size of the hashtable's array;
// key is the key to be found in the array;
// outputs the index of the array cell containing the key (if the table contains it),
// or of the first available cell

static inline
uint32_t fix_htbl_index(term_t* htbl, uint32_t size, term_t key){
  uint32_t result = jenkins_hash_uint32(key) % size;
  while (htbl[result] != NULL_TERM && htbl[result] != key) {
    // We look for the cell containing key, or the first empty cell
    result++;
    result = result % size;
  }
  return result;
}

#ifndef NDEBUG

static inline
bool check_rewrite(plugin_context_t* ctx, term_t old, term_t t){
  if (t == old) return true;
  term_manager_t* tm   = ctx->tm;
  context_t* yctx      = _o_yices_new_context(NULL);
  _o_yices_assert_formula(yctx, mk_neq(tm, old, t));
  smt_status_t output = yices_check_context(yctx, NULL);
  bool result = (output == STATUS_UNSAT);
  if (!result && ctx_trace_enabled(ctx, "mcsat::bv::arith::ctz")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Original term is");
    ctx_trace_term(ctx, old);
    fprintf(out, "New term is");
    ctx_trace_term(ctx, t);
    assert(false);
  }
  _o_yices_free_context(yctx);
  return result;
}

#endif
