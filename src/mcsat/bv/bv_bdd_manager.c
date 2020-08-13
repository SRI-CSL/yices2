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

#include "bv_bdd_manager.h"
#include "bdd_computation.h"
#include "bv_utils.h"
#include "utils/memalloc.h"
#include "utils/int_hash_map.h"
#include "utils/int_hash_sets.h"
#include "utils/ptr_vectors.h"
#include "utils/int_vectors.h"
#include "terms/terms.h"

#include "mcsat/plugin.h"
#include "mcsat/tracing.h"

#ifndef NDEBUG
#define DD_DEBUG
#define DD_STATS
#endif

#include <cudd.h>

/** Null BDD */
const bdd_t bdd_null = { { NULL } };

/** Null BDDs */
const bv_bdd_t bv_bdd_null = { NULL };

/** Information stored about the terms. */
typedef struct {
  /** The term (size of the term is in value.size) */
  term_t t;
  /** Index of the BDDs (only valid if timestamp != 0) */
  uint32_t bdd_index;
  /** Time-stamp of the last BDD change modulo unassigned variable (0 for never) */
  uint32_t bdd_timestamp;
  /** Unit variable of term t, when BDD was computed (NULL if none) */
  term_t unassigned_variable;
  /** The bit-vector value of the term */
  bvconstant_t value;
  /** Time-stamp of the last value change (0 for never) */
  uint32_t value_timestamp;
} term_info_t;

static
void term_info_construct(term_info_t* term_info, term_t t, uint32_t bdd_index, uint32_t bitsize) {
  assert(bitsize > 0);
  term_info->t = t;
  term_info->bdd_index = bdd_index;
  term_info->bdd_timestamp = 0;
  term_info->unassigned_variable = NULL_TERM;
  init_bvconstant(&term_info->value);
  bvconstant_set_bitsize(&term_info->value, bitsize);
  term_info->value_timestamp = 0;
}

static
void term_info_destruct(term_info_t* term_info) {
  delete_bvconstant(&term_info->value);
}

/** All data needed for managing the BDDs. */
struct bv_bdd_manager_s {
  /** Term table */
  const plugin_context_t* ctx;
  /** Cudd manager to be used for all */
  CUDD* cudd;

  /** BDDs per bit */
  pvector_t bdd_variables;

  /** Map from terms to their index in the term_info array */
  int_hmap_t term_to_info_index;

  /** Info on the terms */
  term_info_t* term_info;
  /** Size of the info */
  uint32_t term_info_size;
  /** Capacity of the info */
  uint32_t term_info_capacity;
  /** Timestamp of the last value change */
  uint32_t timestamp;

  /** Vector of all the terms terms added */
  ivector_t term_list;

  /** Memory for storing the BDD pointers */
  BDD** bdd_memory;
  /** BDD memory size */
  uint32_t bdd_memory_size;
  /** BDD memory capacity */
  uint32_t bdd_memory_capacity;

  /** The variable that we consider unassigned when computing */
  term_t unassigned_var;

  /** Marks for visited nodes */
  int_hmap_t visited;

  /** List of terms to recompute the value */
  ivector_t value_recompute;

  /** List of terms to recompute the BDD */
  ivector_t bdd_recompute;

  /** BDD constant false */
  BDD* bdd_false;

  /** BDD constant true */
  BDD* bdd_true;
};

static
void bv_bdd_manager_ensure_variables(bv_bdd_manager_t* bddm, uint32_t bitsize) {
  uint32_t old_size = bddm->bdd_variables.size;
  if (old_size < bitsize) {
    while (bddm->bdd_variables.size < bitsize) {
      pvector_push(&bddm->bdd_variables, NULL);
    }
    bdds_mk_variable(bddm->cudd, (BDD**) bddm->bdd_variables.data + old_size, bitsize - old_size);
  }
}

bv_bdd_manager_t* bv_bdd_manager_new(const plugin_context_t* ctx) {
  // Allocate
  bv_bdd_manager_t* bddm = (bv_bdd_manager_t*) safe_malloc(sizeof(bv_bdd_manager_t));

  bddm->ctx= ctx;
  bddm->cudd = bdds_new();
  bddm->term_info = NULL;
  bddm->term_info_size = 0;
  bddm->term_info_capacity = 0;
  bddm->timestamp = 1;
  bddm->bdd_memory = 0;
  bddm->bdd_memory_size = 0;
  bddm->bdd_memory_capacity = 0;

  init_pvector(&bddm->bdd_variables, 0);

  init_int_hmap(&bddm->term_to_info_index, 0);
  init_ivector(&bddm->term_list, 0);

  bddm->unassigned_var = NULL_TERM;

  init_int_hmap(&bddm->visited, 0);
  init_ivector(&bddm->value_recompute, 0);
  init_ivector(&bddm->bdd_recompute, 0);

  bddm->bdd_false = NULL;
  bddm->bdd_true = NULL;
  bdds_mk_zero(bddm->cudd, &bddm->bdd_false, 1);
  bdds_mk_one(bddm->cudd, &bddm->bdd_true, 1);

  return bddm;
}

bdd_t bv_bdd_manager_true(const bv_bdd_manager_t* bddm) {
  bdd_t result = { { bddm->bdd_true } };
  return result;
}

bdd_t bv_bdd_manager_false(const bv_bdd_manager_t* bddm) {
  bdd_t result = { { bddm->bdd_false } };
  return result;
}

static inline
term_info_t* bv_bdd_manager_get_info(const bv_bdd_manager_t* bddm, term_t t) {
  // Destruct the term info
  int_hmap_pair_t* info_find = int_hmap_find((int_hmap_t*) &bddm->term_to_info_index, t);
  assert(info_find != NULL);
  uint32_t t_info_index = info_find->val;
  term_info_t* t_info = bddm->term_info + t_info_index;
  return t_info;
}

static inline
BDD** bv_bdd_manager_get_bdds_from_info(const bv_bdd_manager_t* bddm, const term_info_t* info) {
  uint32_t bdd_index = info->bdd_index;
  BDD** bdds = bddm->bdd_memory + bdd_index;
  return bdds;
}

static inline
BDD** bv_bdd_manager_get_constant_bdds_from_info(const bv_bdd_manager_t* bddm, const term_info_t* info) {
  uint32_t bdd_index = info->bdd_index;
  BDD** bdds = bddm->bdd_memory + bdd_index + info->value.bitsize;
  return bdds;
}

/**
 * If the term contains the unassigned variable: return term BDDs
 * Otherwise: return constant BDDs
 */
static inline
BDD** bv_bdd_manager_get_bdds(bv_bdd_manager_t* bddm, term_t t) {
  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);
  int_hmap_pair_t* find = int_hmap_find(&bddm->visited, t);
  assert(find != NULL);
  if (find->val) {
    // Contains the unassigned variable, so we get the BDDs
    return bv_bdd_manager_get_bdds_from_info(bddm, t_info);
  } else {
    // Convert the value to BDD
    const bvconstant_t* value = &t_info->value;
    BDD** out = bv_bdd_manager_get_constant_bdds_from_info(bddm, t_info);
    bdds_clear(bddm->cudd, out, value->bitsize);
    bdds_mk_constant(bddm->cudd, out, value->bitsize, value);
    return out;
  }
}

void bv_bdd_manager_delete(bv_bdd_manager_t* bddm) {

  term_table_t* terms = bddm->ctx->terms;
  CUDD* cudd = bddm->cudd;

  // Decrease reference counts and destruct all term info
  for (uint32_t i = 0; i < bddm->term_list.size; ++ i) {
    // Term and info
    term_t t = bddm->term_list.data[i];
    uint32_t t_bitsize = bv_term_bitsize(terms, t);
    term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);
    assert(t_bitsize == t_info->value.bitsize);
    BDD** t_bdd_memory = bv_bdd_manager_get_bdds_from_info(bddm, t_info);
    uint32_t allocated_size = 2*t_bitsize;
    bdds_clear(cudd, t_bdd_memory, allocated_size);
    term_info_destruct(t_info);
  }

  bdds_clear(bddm->cudd, (BDD**) bddm->bdd_variables.data, bddm->bdd_variables.size);
  delete_pvector(&bddm->bdd_variables);

  delete_int_hmap(&bddm->term_to_info_index);
  delete_ivector(&bddm->term_list);

  delete_int_hmap(&bddm->visited);
  delete_ivector(&bddm->value_recompute);
  delete_ivector(&bddm->bdd_recompute);

  bdds_clear(cudd, &bddm->bdd_false, 1);
  bdds_clear(cudd, &bddm->bdd_true, 1);

  bdds_delete(bddm->cudd);

  safe_free(bddm->term_info);
  safe_free(bddm->bdd_memory);
  safe_free(bddm);
}

#define BV_BDD_MEM_DEFAULT_SIZE 10
#define BV_BDD_MEM_MAX_SIZE (UINT32_MAX/8)

static
void bv_bdd_manager_ensure_term_capacity(bv_bdd_manager_t* bddm, uint32_t var_index) {
  uint32_t n;
  while (bddm->term_info_capacity <= var_index) {
    n = bddm->term_info_capacity;
    if (n == 0) {
      n = BV_BDD_MEM_DEFAULT_SIZE;
    } else {
      n ++;
      n += n >> 1;
      if (n >= BV_BDD_MEM_MAX_SIZE) {
        out_of_memory();
      }
    }
    bddm->term_info = (term_info_t*) safe_realloc(bddm->term_info, n*sizeof(term_info_t));
    bddm->term_info_capacity = n;
  }
}

static
void bv_bdd_manager_ensure_bdd_capacity(bv_bdd_manager_t* bddm, uint32_t term_index) {
  uint32_t n;
  while (bddm->bdd_memory_capacity <= term_index) {
    n = bddm->bdd_memory_capacity;
    if (n == 0) {
      n = BV_BDD_MEM_DEFAULT_SIZE;
    } else {
      n ++;
      n += n >> 1;
      if (n >= BV_BDD_MEM_MAX_SIZE) {
        out_of_memory();
      }
    }
    bddm->bdd_memory = (BDD**) safe_realloc(bddm->bdd_memory, n*sizeof(BDD*));
    bddm->bdd_memory_capacity = n;
  }
}

bool bv_bdd_manager_has_term(const bv_bdd_manager_t* bddm, term_t term) {
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &bddm->term_to_info_index, term);
  return (find != NULL);
}

uint32_t bv_bdd_manager_allocate_term_info(bv_bdd_manager_t* bddm, term_t t, uint32_t bitsize) {

  assert(int_hmap_find(&bddm->term_to_info_index, t) == NULL);
  assert(bv_term_bitsize(bddm->ctx->terms, t) == bitsize);

  // Add the reference for t
  uint32_t t_info_index = bddm->term_info_size;
  int_hmap_add(&bddm->term_to_info_index, t, t_info_index);
  // Make sure there is enough memory
  bv_bdd_manager_ensure_term_capacity(bddm, t_info_index);
  // Increase the size
  term_info_t* x_info = bddm->term_info + t_info_index;
  bddm->term_info_size ++;
  // Add the BDD reference for t
  uint32_t t_bdd_index = bddm->bdd_memory_size;
  // Make sure there is enough memory (bitsize for non-value + bitsize for value)
  uint32_t bdd_allocate_size = 2*bitsize;
  bv_bdd_manager_ensure_bdd_capacity(bddm, t_bdd_index + bdd_allocate_size);
  // Construct: set all BDDs to null
  BDD** t_bdds = bddm->bdd_memory + t_bdd_index;
  bddm->bdd_memory_size += bdd_allocate_size;
  bdds_init(t_bdds, bdd_allocate_size);
  // Construct info
  term_info_construct(x_info, t, t_bdd_index, bitsize);
  // Remember the allocated terms
  ivector_push(&bddm->term_list, t);

  return t_info_index;
}

/**
 * Recursively allocate the data for all bit-vector terms in t.
 */
static
void bv_bdd_manager_ensure_term_data(bv_bdd_manager_t* bddm, term_t t, uint32_t bitsize) {

  term_table_t* terms = bddm->ctx->terms;

  int_hmap_pair_t* info_index_find = int_hmap_find(&bddm->term_to_info_index, t);
  if (info_index_find == NULL) {

    if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
      ctx_trace_printf(bddm->ctx, "bv_bdd_manager: allocating term/BDD data for ");
      ctx_trace_term(bddm->ctx, t);
    }

    // Allocate this term
    uint32_t t_info_index = bv_bdd_manager_allocate_term_info(bddm, t, bitsize);
    term_info_t* t_info = bddm->term_info + t_info_index;
    BDD** t_bdds = bv_bdd_manager_get_bdds_from_info(bddm, t_info);

    // Ensure data for the sub-terms
    if (is_neg_term(t)) {
      term_t t_pos = unsigned_term(t);
      bv_bdd_manager_ensure_term_data(bddm, t_pos, bitsize);
    } else {
      bool handle_variable = false;
      term_kind_t t_kind = term_kind(terms, t);
      switch (t_kind) {
      case EQ_TERM: { // Boolean equality only
        composite_term_t* eq = eq_term_desc(terms, t);
        term_t lhs = eq->arg[0];
        term_t rhs = eq->arg[1];
        if (is_boolean_term(terms, lhs) || is_bitvector_term(terms, lhs)) {
          bv_bdd_manager_ensure_term_data(bddm, lhs, 1);
          bv_bdd_manager_ensure_term_data(bddm, rhs, 1);
        } else {
	  handle_variable = true;
        }
        break;
      }
      case OR_TERM: // Boolean
      case XOR_TERM: // Boolean
      case BV_EQ_ATOM:
      case BV_GE_ATOM:
      case BV_SGE_ATOM: {
        // Boolean atoms, children are bitvectors
        assert(bitsize == 1);
        composite_term_t* atom_comp = composite_term_desc(terms, t);
        for (uint32_t i = 0; i < atom_comp->arity; ++ i) {
          uint32_t child_bitsize = bv_term_bitsize(terms, atom_comp->arg[i]);
          bv_bdd_manager_ensure_term_data(bddm, atom_comp->arg[i], child_bitsize);
        }
        break;
      }
      case BV_ARRAY:
      case BV_DIV:
      case BV_REM:
      case BV_SDIV:
      case BV_SREM:
      case BV_SMOD:
      case BV_SHL:
      case BV_LSHR:
      case BV_ASHR: {
        // Ensure data for children
        composite_term_t* t_comp = composite_term_desc(terms, t);
        for (uint32_t i = 0; i < t_comp->arity; ++ i) {
          uint32_t t_i_bitsize = bv_term_bitsize(terms, t_comp->arg[i]);
          assert(t_kind == BV_ARRAY || t_i_bitsize == bitsize);
          assert(t_kind != BV_ARRAY || t_i_bitsize == 1);
          bv_bdd_manager_ensure_term_data(bddm, t_comp->arg[i], t_i_bitsize);
        }
        break;
      }
      case BIT_TERM: {
        select_term_t* desc = bit_term_desc(terms, t);
        term_t child = desc->arg;
        uint32_t child_bitsize = bv_term_bitsize(terms, child);
        bv_bdd_manager_ensure_term_data(bddm, child, child_bitsize);
        break;
      }
      case BV_POLY: {
        // Polynomial, allocate data for the subterms (variables)
        bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
        for (uint32_t i = 0; i < t_poly->nterms; ++i) {
          if (t_poly->mono[i].var == const_idx) continue;
          term_t var = t_poly->mono[i].var;
          assert(bv_term_bitsize(terms, var) == bitsize);
          bv_bdd_manager_ensure_term_data(bddm, var, bitsize);
        }
        break;
      }
      case BV64_POLY: {
        // Polynomial, allocate data for the subterms (variables)
        bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
        for (uint32_t i = 0; i < t_poly->nterms; ++i) {
          if (t_poly->mono[i].var == const_idx) continue;
          term_t var = t_poly->mono[i].var;
          assert(bv_term_bitsize(terms, var) == bitsize);
          bv_bdd_manager_ensure_term_data(bddm, var, bitsize);
        }
        break;
      }
      case POWER_PRODUCT: {
        pprod_t* t_pprod = pprod_term_desc(terms, t);
        for (uint32_t i = 0; i < t_pprod->len; ++ i) {
          term_t var = t_pprod->prod[i].var;
          assert(bv_term_bitsize(terms, var) == bitsize);
          bv_bdd_manager_ensure_term_data(bddm, var, bitsize);
        }
        break;
      }
      case CONSTANT_TERM:
        if (t == true_term) {
          bvconst_set_bit(t_info->value.data, 0);
        } else if (t == false_term) {
          bvconst_clr_bit(t_info->value.data, 0);
        } else {
          assert(false); // Only Boolean constants
        }
        t_info->value_timestamp = 1;
        break;
      case BV_CONSTANT: {
        // Set the value
        bvconst_term_t* t_desc = bvconst_term_desc(terms, t);
        bvconstant_copy(&t_info->value, t_desc->bitsize, t_desc->data);
        t_info->value_timestamp = 1;
        break;
      }
      case BV64_CONSTANT: {
        // Set the value
        bvconst64_term_t* t_desc = bvconst64_term_desc(terms, t);
        bvconstant_copy64(&t_info->value, t_desc->bitsize, t_desc->value);
        t_info->value_timestamp = 1;
        break;
      }
      default:
        handle_variable = true;
        break;
      }

      if (handle_variable) {
        // Add the variables nodes
        bv_bdd_manager_ensure_variables(bddm, bitsize);
        bdds_copy(t_bdds, (BDD**) bddm->bdd_variables.data, bitsize);
        // Mark the info for this variable
        t_info->unassigned_variable = t;
        t_info->bdd_timestamp = 1;
      }
    }
  } else {
    assert(info_index_find != NULL);
  }
}

void bv_bdd_manager_add_term(bv_bdd_manager_t* bddm, term_t t) {
  uint32_t bitsize = bv_term_bitsize(bddm->ctx->terms, t);
  bv_bdd_manager_ensure_term_data(bddm, t, bitsize);
}

/**
 * Go through the term and:
 * - compute the value and value timestamp of each subterm that evaluates
 * - compute the BDD timestamp of each subterm
 * - if the BDD needs to be recomputed, put it in the list
 *
 * Returns true if the term contains the unassigned variable.
 *
 * If the return value is true the value timestamp should be ignored.
 * If the return value is false the BDD timestamp should be ignored.
 */
static
bool bv_bdd_manager_recompute_timestamps(bv_bdd_manager_t* bddm, term_t t, uint32_t bitsize, uint32_t* bdd_timestamp, uint32_t* value_timestamp) {

  term_table_t* terms = bddm->ctx->terms;

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: recomputing timestamps for ");
    ctx_trace_term(bddm->ctx, t);
  }

  // Info for t
  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);

  // If visited already, skip
  int_hmap_pair_t* find = int_hmap_find(&bddm->visited, t);
  if (find != NULL) {
    *bdd_timestamp = t_info->bdd_timestamp;
    *value_timestamp = t_info->value_timestamp;
    return find->val;
  }

  // Does this term contain the unassigned variable
  bool contains_unassigned = false;

  // Variables: timestamps and values are always OK, we set them manually
  if (bv_term_is_variable(terms, t)) {
    *value_timestamp = t_info->value_timestamp;
    *bdd_timestamp = t_info->bdd_timestamp;
    assert(*bdd_timestamp == 1);
    contains_unassigned = (t == bddm->unassigned_var);
    int_hmap_add(&bddm->visited, t, contains_unassigned);
    return contains_unassigned;
  }

  // Initialize the timestamps
  *bdd_timestamp = 0;
  *value_timestamp = 0;

  // Should we recompute value
  bool recompute_value = false;

  // Should we recompute BDD
  bool recompute_bdd = false;

  // Negation
  if (is_neg_term(t)) {
    contains_unassigned = bv_bdd_manager_recompute_timestamps(bddm, unsigned_term(t), bitsize, bdd_timestamp, value_timestamp);
  } else {
    term_kind_t t_kind = term_kind(terms, t);
    switch (t_kind) {
    case OR_TERM: // Boolean OR
    case XOR_TERM: // Boolean XOR
    case EQ_TERM: // Boolean equality
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR: {
      // Get the children BDDs
      composite_term_t* t_comp = composite_term_desc(terms, t);
      for (uint32_t i = 0; i < t_comp->arity; ++i) {
        uint32_t bdd_timestamp_i = 0;
        uint32_t value_timestamp_i = 0;
        uint32_t t_i = t_comp->arg[i];
        uint32_t bitsize_i = bv_term_bitsize(terms, t_i);
        bool t_i_contains_unassigned = bv_bdd_manager_recompute_timestamps(bddm, t_i, bitsize_i, &bdd_timestamp_i, &value_timestamp_i);
        contains_unassigned = contains_unassigned || t_i_contains_unassigned;
        if (bdd_timestamp_i > *bdd_timestamp) { *bdd_timestamp = bdd_timestamp_i; }
        if (value_timestamp_i > *value_timestamp) { *value_timestamp = value_timestamp_i; }
      }
      break;
    }
    case BIT_TERM:
      contains_unassigned = bv_bdd_manager_recompute_timestamps(bddm, bit_term_arg(terms, t), 1, bdd_timestamp, value_timestamp);
      break;
    case BV_POLY: {
      bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++i) {
        if (t_poly->mono[i].var == const_idx) continue;
        uint32_t bdd_timestamp_i = 0;
        uint32_t value_timestamp_i = 0;
        term_t t_i = t_poly->mono[i].var;
        uint32_t bitsize_i = bv_term_bitsize(terms, t_i);
        bool t_i_contains_unassigned = bv_bdd_manager_recompute_timestamps(bddm, t_i, bitsize_i, &bdd_timestamp_i, &value_timestamp_i);
        contains_unassigned = contains_unassigned || t_i_contains_unassigned;
        if (bdd_timestamp_i > *bdd_timestamp) { *bdd_timestamp = bdd_timestamp_i; }
        if (value_timestamp_i > *value_timestamp) { *value_timestamp = value_timestamp_i; }
      }
      break;
    }
    case BV64_POLY: {
      // Polynomial, allocate data for the subterms (variables)
      bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++i) {
        if (t_poly->mono[i].var == const_idx) continue;
        uint32_t bdd_timestamp_i = 0;
        uint32_t value_timestamp_i = 0;
        term_t t_i = t_poly->mono[i].var;
        uint32_t bitsize_i = bv_term_bitsize(terms, t_i);
        bool t_i_contains_unassigned = bv_bdd_manager_recompute_timestamps(bddm, t_i, bitsize_i, &bdd_timestamp_i, &value_timestamp_i);
        contains_unassigned = contains_unassigned || t_i_contains_unassigned;
        if (bdd_timestamp_i > *bdd_timestamp) { *bdd_timestamp = bdd_timestamp_i; }
        if (value_timestamp_i > *value_timestamp) { *value_timestamp = value_timestamp_i; }
      }
      break;
    }
    case POWER_PRODUCT: {
      pprod_t* t_pprod = pprod_term_desc(terms, t);
      for (uint32_t i = 0; i < t_pprod->len; ++ i) {
        uint32_t bdd_timestamp_i = 0;
        uint32_t value_timestamp_i = 0;
        term_t t_i = t_pprod->prod[i].var;
        uint32_t bitsize_i = bv_term_bitsize(terms, t_i);
        bool t_i_contains_unassigned = bv_bdd_manager_recompute_timestamps(bddm, t_i, bitsize_i, &bdd_timestamp_i, &value_timestamp_i);
        contains_unassigned = contains_unassigned || t_i_contains_unassigned;
        if (bdd_timestamp_i > *bdd_timestamp) { *bdd_timestamp = bdd_timestamp_i; }
        if (value_timestamp_i > *value_timestamp) { *value_timestamp = value_timestamp_i; }
      }
      break;
    }
    case CONSTANT_TERM:
    case BV_CONSTANT:
    case BV64_CONSTANT:
      // Nothing to do, always constant
      *bdd_timestamp = 1;
      *value_timestamp = 1;
      contains_unassigned = false;
      break;
    default:
      // Shouldn't be here, variables handled above
      assert(false);
    }
  }

  // Should we recompute
  recompute_value = !contains_unassigned &&
      (t_info->value_timestamp != *value_timestamp);
  recompute_bdd = contains_unassigned &&
      (t_info->bdd_timestamp != *bdd_timestamp || t_info->unassigned_variable != bddm->unassigned_var);
  // Set the timestamps
  if (recompute_value) {
    t_info->value_timestamp = *value_timestamp;
    ivector_push(&bddm->value_recompute, t);
  }
  if (recompute_bdd) {
    t_info->bdd_timestamp = *bdd_timestamp;
    ivector_push(&bddm->bdd_recompute, t);
  }

  // Mark as visited
  int_hmap_add(&bddm->visited, t, contains_unassigned);

  return contains_unassigned;
}

static inline
bvconstant_t* bv_bdd_manager_get_value(bv_bdd_manager_t* bddm, term_t t) {
  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);
  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "value of ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, "value = ");
    bvconst_print(ctx_trace_out(bddm->ctx), t_info->value.data, t_info->value.bitsize);
    ctx_trace_printf(bddm->ctx, "\n");
  }
  return &t_info->value;
}

static inline
void bv_bdd_manager_compute_value(bv_bdd_manager_t* bddm, term_t t) {

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: computing value for ");
    ctx_trace_term(bddm->ctx, t);
  }

  uint32_t i;
  term_t t_i;
  bvconstant_t* value_i;
  term_table_t* terms = bddm->ctx->terms;

  pvector_t children_values;
  init_pvector(&children_values, 0);

  // Negation
  if (is_neg_term(t)) {
    t_i = unsigned_term(t);
    value_i = bv_bdd_manager_get_value(bddm, t_i);
    pvector_push(&children_values, value_i);
  } else {
    term_kind_t t_kind = term_kind(terms, t);
    switch (t_kind) {
    case OR_TERM:
    case XOR_TERM:
    case EQ_TERM:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR: {
      // Get the children BDDs
      composite_term_t* t_comp = composite_term_desc(terms, t);
      for (i = 0; i < t_comp->arity; ++i) {
        t_i = t_comp->arg[i];
        value_i = bv_bdd_manager_get_value(bddm, t_i);
        pvector_push(&children_values, value_i);
      }
      break;
    }
    case BIT_TERM:
      t_i = bit_term_arg(terms, t);
      value_i = bv_bdd_manager_get_value(bddm, t_i);
      pvector_push(&children_values, value_i);
      break;
    case BV_POLY: {
      bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++i) {
        if (t_poly->mono[i].var == const_idx) continue;
        t_i = t_poly->mono[i].var;
        value_i = bv_bdd_manager_get_value(bddm, t_i);
        pvector_push(&children_values, value_i);
      }
      break;
    }
    case BV64_POLY: {
      // Polynomial, allocate data for the subterms (variables)
      bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++i) {
        if (t_poly->mono[i].var == const_idx) continue;
        t_i = t_poly->mono[i].var;
        value_i = bv_bdd_manager_get_value(bddm, t_i);
        pvector_push(&children_values, value_i);
      }
      break;
    }
    case POWER_PRODUCT:{
      pprod_t* t_pprod = pprod_term_desc(terms, t);
      for (uint32_t i = 0; i < t_pprod->len; ++ i) {
        term_t t_i = t_pprod->prod[i].var;
        value_i = bv_bdd_manager_get_value(bddm, t_i);
        pvector_push(&children_values, value_i);
      }
      break;
    }
    default:
      // Shouldn't be here
      assert(false);
    }
  }

  // We have the children values compute
  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);
  bv_term_compute_value(terms, t, (bvconstant_t**) children_values.data, &t_info->value);

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: new value for ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, "value = ");
    bvconst_print(ctx_trace_out(bddm->ctx), t_info->value.data, t_info->value.bitsize);
    ctx_trace_printf(bddm->ctx, "\n");
  }

  // Remove temp
  delete_pvector(&children_values);
}

static inline
void bv_bdd_manager_compute_bdd(bv_bdd_manager_t* bddm, term_t t) {

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: computing BDD for ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, "unassigned variable: ");
    ctx_trace_term(bddm->ctx, bddm->unassigned_var);
  }

  uint32_t i;
  term_t t_i;
  BDD** bdds_i;
  term_table_t* terms = bddm->ctx->terms;
  CUDD* cudd = bddm->cudd;

  // We store children BDD pointers here
  pvector_t children_bdds;
  init_pvector(&children_bdds, 0);

  // Term data
  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);
  BDD** t_bdds = bv_bdd_manager_get_bdds_from_info(bddm, t_info);

  // Remove all previous BDDs
  uint32_t bitsize = bv_term_bitsize(terms, t);
  bdds_clear(cudd, t_bdds, bitsize);

  // Negation
  if (is_neg_term(t)) {
    t_i = unsigned_term(t);
    bdds_i = bv_bdd_manager_get_bdds(bddm, t_i);
    pvector_push(&children_bdds, bdds_i);
  } else {
    term_kind_t t_kind = term_kind(terms, t);

    // First, get all the children BDDs
    switch (t_kind) {
    case OR_TERM:
    case XOR_TERM:
    case EQ_TERM:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR: {
      // Get the children BDDs
      composite_term_t* t_comp = composite_term_desc(terms, t);
      for (i = 0; i < t_comp->arity; ++i) {
        t_i = t_comp->arg[i];
        bdds_i = bv_bdd_manager_get_bdds(bddm, t_i);
        pvector_push(&children_bdds, bdds_i);
      }
      break;
    }
    case BIT_TERM:
      t_i = bit_term_arg(terms, t);
      bdds_i = bv_bdd_manager_get_bdds(bddm, t_i);
      pvector_push(&children_bdds, bdds_i);
      break;
    case BV_POLY: {
      bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++i) {
        if (t_poly->mono[i].var == const_idx) continue;
        t_i = t_poly->mono[i].var;
        bdds_i = bv_bdd_manager_get_bdds(bddm, t_i);
        pvector_push(&children_bdds, bdds_i);
      }
      break;
    }
    case BV64_POLY: {
      // Polynomial, allocate data for the subterms (variables)
      bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++i) {
        if (t_poly->mono[i].var == const_idx) continue;
        t_i = t_poly->mono[i].var;
        bdds_i = bv_bdd_manager_get_bdds(bddm, t_i);
        pvector_push(&children_bdds, bdds_i);
      }
      break;
    }
    case POWER_PRODUCT: {
      pprod_t* t_pprod = pprod_term_desc(terms, t);
      for (uint32_t i = 0; i < t_pprod->len; ++ i) {
        t_i = t_pprod->prod[i].var;
        bdds_i = bv_bdd_manager_get_bdds(bddm, t_i);
        pvector_push(&children_bdds, bdds_i);
      }
      break;
    }
    default:
      // Shouldn't be here
      assert(false);
    }
  }

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
//    FILE* out = ctx_trace_out(bddm->ctx);
//    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: computing BDDs ");
//    ctx_trace_term(bddm->ctx, t);
//    ctx_trace_printf(bddm->ctx, "unassigned variable: ");
//    ctx_trace_term(bddm->ctx, bddm->unassigned_var);
//    ctx_trace_printf(bddm->ctx, "x BDDs: ");
//    term_info_t* x_info = bv_bdd_manager_get_info(bddm, bddm->unassigned_var);
//    BDD** x_bdds = bv_bdd_manager_get_bdds_from_info(bddm, x_info);
//    bdds_print(bddm->cudd, x_bdds, x_info->value.bitsize, out);
//    for (int i = 0; i < children_bdds.size; ++ i) {
//      ctx_trace_printf(bddm->ctx, "\nchildren[%d] BDDs: ", i);
//      bdds_print(bddm->cudd, children_bdds.data[i], bitsize, out);
//      ctx_trace_printf(bddm->ctx, "\n");
//    }
  }

  // We have the children values compute
  bdds_compute_bdds(bddm->cudd, terms, t, &children_bdds, t_bdds);

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: BDD done for ");
    ctx_trace_term(bddm->ctx, t);
//    ctx_trace_printf(bddm->ctx, "unassigned variable: ");
//    ctx_trace_term(bddm->ctx, bddm->unassigned_var);
//    ctx_trace_printf(bddm->ctx, "x BDDs: ");
//    term_info_t* x_info = bv_bdd_manager_get_info(bddm, bddm->unassigned_var);
//    BDD** x_bdds = bv_bdd_manager_get_bdds_from_info(bddm, x_info);
//    bdds_print(bddm->cudd, x_bdds, x_info->value.bitsize, ctx_trace_out(bddm->ctx));
//    ctx_trace_printf(bddm->ctx, "\nt BDDs: ");
//    bdds_print(bddm->cudd, t_bdds, bitsize, ctx_trace_out(bddm->ctx));
//    ctx_trace_printf(bddm->ctx, "\n");
  }

  // Remove temp
  delete_pvector(&children_bdds);
}

BDD** bv_bdd_manager_get_term_bdds(bv_bdd_manager_t* bddm, term_t t, uint32_t bitsize) {

  uint32_t i;
  term_t t_recompute;

  assert(bddm->visited.nelems == 0);
  assert(bddm->bdd_recompute.size == 0);
  assert(bddm->value_recompute.size == 0);

  // Make sure we have allocated the data for t
  bv_bdd_manager_ensure_term_data(bddm, t, bitsize);

  // Recompute timestamps
  uint32_t bdd_timestamp = 0, value_timestamp = 0;
  bool contains_unassigned = bv_bdd_manager_recompute_timestamps(bddm, t, bitsize, &bdd_timestamp, &value_timestamp);
  (void) contains_unassigned;
  assert(contains_unassigned);

  // Recompute needed values
  for (i = 0; i < bddm->value_recompute.size; ++ i) {
    t_recompute = bddm->value_recompute.data[i];
    bv_bdd_manager_compute_value(bddm, t_recompute);
  }

  // Recompute needed BDDs
  for (i = 0; i < bddm->bdd_recompute.size; ++ i) {
    assert(i == 0 || t_recompute != bddm->bdd_recompute.data[i]);
    t_recompute = bddm->bdd_recompute.data[i];
    bv_bdd_manager_compute_bdd(bddm, t_recompute);
  }

  // Clear the cache
  int_hmap_reset(&bddm->visited);
  ivector_reset(&bddm->bdd_recompute);
  ivector_reset(&bddm->value_recompute);

  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);
  BDD** t_bdds = bv_bdd_manager_get_bdds_from_info(bddm, t_info);

  // Return the BDDs
  return t_bdds;
}

void bv_bdd_manager_set_bv_value(bv_bdd_manager_t* bddm, term_t t, const bvconstant_t* value) {
  assert(bv_term_get_type(bddm->ctx->terms, t) == BV_TERM_VARIABLE);
  assert(bv_term_bitsize(bddm->ctx->terms, t) == value->bitsize);

  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);
  assert(t_info->value.bitsize == value->bitsize);

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: setting bit value for ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, "value = ");
    bvconst_print(ctx_trace_out(bddm->ctx), value->data, value->bitsize);
    ctx_trace_printf(bddm->ctx, "\nold_value = ");
    bvconst_print(ctx_trace_out(bddm->ctx), t_info->value.data, t_info->value.bitsize);
    ctx_trace_printf(bddm->ctx, "\n");
  }

  if (t_info->value_timestamp == 0 || !bvconst_eq(t_info->value.data, value->data, value->width)) {
    bvconstant_copy(&t_info->value, value->bitsize, value->data);
    t_info->value_timestamp = ++ bddm->timestamp;
  }

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "set value = ");
    bvconst_print(ctx_trace_out(bddm->ctx), t_info->value.data, t_info->value.bitsize);
    ctx_trace_printf(bddm->ctx, "\n");
  }
}

void bv_bdd_manager_set_bool_value(bv_bdd_manager_t* bddm, term_t t, bool value) {
  assert(bv_term_get_type(bddm->ctx->terms, t) == BV_TERM_VARIABLE);
  assert(bv_term_bitsize(bddm->ctx->terms, t) == 1);

  term_info_t* t_info = bv_bdd_manager_get_info(bddm, t);

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: setting bit value for ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, "value = %s\n", (value ? "true" : "false"));
    ctx_trace_printf(bddm->ctx, "old_value = ");
    bvconst_print(ctx_trace_out(bddm->ctx), t_info->value.data, t_info->value.bitsize);
    ctx_trace_printf(bddm->ctx, "\n");
  }

  assert(t_info->value.bitsize == 1);

  if (t_info->value_timestamp == 0 || bvconst_tst_bit(t_info->value.data, 0) != value) {
    if (value) {
      bvconst_set_bit(t_info->value.data, 0);
    } else {
      bvconst_clr_bit(t_info->value.data, 0);
    }
    t_info->value_timestamp = ++ bddm->timestamp;
  }

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "set value = ");
    bvconst_print(ctx_trace_out(bddm->ctx), t_info->value.data, t_info->value.bitsize);
    ctx_trace_printf(bddm->ctx, "\n");
  }
}

bdd_t bv_bdd_manager_get_bdd(bv_bdd_manager_t* bddm, term_t t, term_t x) {

  bdd_t result = bdd_null;

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: creating BDD for ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, "unit in variable ");
    ctx_trace_term(bddm->ctx, x);
  }

  // Set the unit variable
  assert(bddm->unassigned_var == NULL_TERM);
  bddm->unassigned_var = x;

  // Compute
  assert(is_boolean_term(bddm->ctx->terms, t));
  BDD** t_bdds = bv_bdd_manager_get_term_bdds(bddm, t, 1);
  result.bdd[0] = t_bdds[0];

  // Unset the unit variable
  bddm->unassigned_var = NULL_TERM;

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: BDD for ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, "unit in variable ");
    ctx_trace_term(bddm->ctx, x);
    bv_bdd_manager_bdd_print(bddm, result, ctx_trace_out(bddm->ctx));
    ctx_trace_printf(bddm->ctx, "\n");
  }

  return result;
}

bv_bdd_t bv_bdd_manager_get_bv_bdd(bv_bdd_manager_t* bddm, term_t t, term_t x) {

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "creating BDD for ");
    ctx_trace_term(bddm->ctx, t);
    ctx_trace_printf(bddm->ctx, " in variable");
    ctx_trace_term(bddm->ctx, x);
  }

  // Set the unit variable
  assert(bddm->unassigned_var == NULL_TERM);
  bddm->unassigned_var = x;

  assert(is_bitvector_term(bddm->ctx->terms, t));

  bv_bdd_t result = bv_bdd_null;
  uint32_t t_bitsize = bv_term_bitsize(bddm->ctx->terms, t);
  BDD** t_bdds = bv_bdd_manager_get_term_bdds(bddm, t, t_bitsize);
  result.bdds = (void**) t_bdds;

  // Unset the unit variable
  bddm->unassigned_var = NULL_TERM;

  return result;
}

void bv_bdd_manager_bdd_detach(bv_bdd_manager_t* bddm, bdd_t bdd) {
  bdds_clear(bddm->cudd, (BDD**) bdd.bdd, 1);
}

void bv_bdd_manager_bdd_attach(bv_bdd_manager_t* bddm, bdd_t bdd) {
  bdds_attach((BDD**) bdd.bdd, 1);
}

void bv_bdd_manager_bdd_print(const bv_bdd_manager_t* bddm, bdd_t bdd, FILE* out) {
  bdds_print(bddm->cudd, (BDD**) bdd.bdd, 1, out);
}

bool bv_bdd_manager_bdd_is_empty(const bv_bdd_manager_t* bddm, bdd_t bdd) {
  // Check that BDD != false, i.e., there is an assignment so that it is true
  assert(bdd.bdd[0] != NULL);
  return bdd.bdd[0] == bddm->bdd_false;
}

bool bv_bdd_manager_bdd_is_point(const bv_bdd_manager_t* bddm, bdd_t bdd, uint32_t bitsize) {

  if (ctx_trace_enabled(bddm->ctx, "mcsat::bv::bdd")) {
    ctx_trace_printf(bddm->ctx, "bv_bdd_manager: checking if point: ");
    bdds_print(bddm->cudd, (BDD**) bdd.bdd, 1, ctx_trace_out(bddm->ctx));
    ctx_trace_printf(bddm->ctx, "\n");
  }

  // Check if BDD is a point: has to be a cube
  return bdds_is_point(bddm->cudd, (BDD*) bdd.bdd[0], bitsize);
}

bdd_t bv_bdd_manager_bdd_intersect(bv_bdd_manager_t* bddm, bdd_t bdd1, bdd_t bdd2) {
  assert(bdd1.bdd[0] != NULL);
  assert(bdd2.bdd[0] != NULL);
  bdd_t bdd = { { NULL } };
  bdds_mk_and(bddm->cudd, (BDD**) bdd.bdd, (BDD**) bdd1.bdd, (BDD**) &bdd2.bdd, 1);
  return bdd;
}

void bv_bdd_manager_pick_value(bv_bdd_manager_t* bddm, term_t x, bdd_t bdd, bvconstant_t* out) {
  term_info_t* x_info = bv_bdd_manager_get_info(bddm, x);
  const bvconstant_t* prev_value = &x_info->value;
  BDD** x_bdds = bv_bdd_manager_get_bdds_from_info(bddm, x_info);
  assert(out->bitsize == prev_value->bitsize);
  if (bdds_is_model(bddm->cudd, x_bdds, (BDD*) bdd.bdd[0], prev_value)) {
    // If cached value works, just use it
    bvconstant_copy(out, out->bitsize, prev_value->data);
  } else {
    bdds_get_model(bddm->cudd, x_bdds, (BDD*) bdd.bdd[0], out);
  }
}

bool bv_bdd_manager_is_model(bv_bdd_manager_t* bddm, term_t x, bdd_t bdd, const bvconstant_t* x_value) {
  term_info_t* x_info = bv_bdd_manager_get_info(bddm, x);
  BDD** x_bdds = bv_bdd_manager_get_bdds_from_info(bddm, x_info);
  return bdds_is_model(bddm->cudd, x_bdds, (BDD*) bdd.bdd[0], x_value);
}

void bv_bdd_manager_mark_terms(bv_bdd_manager_t* bddm) {
  uint32_t i;
  for (i = 0; i < bddm->term_list.size; ++ i) {
    term_t t = bddm->term_list.data[i];
    term_table_set_gc_mark(bddm->ctx->terms, index_of(t));
  }
}
