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

#include <stdio.h>

#include "terms/terms.h"
#include "mcsat/value.h"

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
uint32_t bv_term_bitsize(term_table_t* terms, term_t t) {
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
  return bv_term_get_type(terms, t) == BV_TERM_VARIABLE;
}

/** Construct a MCSAT value from a constant term */
static inline
void mcsat_value_construct_from_bv(mcsat_value_t* t_value, term_table_t* terms, term_t t) {
  term_kind_t t_kind = term_kind(terms, t);
  if (t_kind == BV_CONSTANT) {
    // Propagate constant value (it's first time we see it, so should be safe
    bvconst_term_t* t_desc = bvconst_term_desc(terms, t);
    bvconstant_t t_bvconst;
    init_bvconstant(&t_bvconst);
    bvconstant_set_bitsize(&t_bvconst, t_desc->bitsize);
    bvconstant_copy(&t_bvconst, t_desc->bitsize, t_desc->data);
    mcsat_value_construct_bv_value(t_value, &t_bvconst);
    delete_bvconstant(&t_bvconst);
  } else if (t_kind == BV64_CONSTANT) {
    // Propagate constant value (it's first time we see it, so should be safe
    bvconst64_term_t* t_desc = bvconst64_term_desc(terms, t);
    bvconstant_t t_bvconst;
    init_bvconstant(&t_bvconst);
    bvconstant_set_bitsize(&t_bvconst, t_desc->bitsize);
    bvconstant_copy64(&t_bvconst, t_desc->bitsize, t_desc->value);
    mcsat_value_construct_bv_value(t_value, &t_bvconst);
    delete_bvconstant(&t_bvconst);
  } else if (t_kind == CONSTANT_TERM) {
    assert(t == true_term || t == false_term);
    mcsat_value_construct_bool(t_value, t == true_term);
  } else {
    assert(false);
  }
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
    case BV_DIV:
      bvconst_udiv2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      break;
    case BV_REM:
      bvconst_urem2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      break;
    case BV_SDIV:
      bvconst_sdiv2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      break;
    case BV_SREM:
      bvconst_srem2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
      break;
    case BV_SMOD:
      bvconst_smod2z(out_value->data, bitsize, children_values[0]->data, children_values[1]->data);
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
          uint64_t t_i_64_value = bvconst_get64(t_i_value->data);
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

