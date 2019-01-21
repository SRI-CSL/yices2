/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#pragma once

#include "mcsat/tracing.h"
#include "mcsat/mcsat_types.h"
#include "mcsat/eq/equality_graph.h"

#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"

#include "utils/ptr_queues.h"
#include "utils/ptr_hash_map.h"

typedef struct slice_s slice_t;

/* Pair of slices (equality or disequality) */
typedef struct {
  slice_t* lhs;
  slice_t* rhs;
  /** Whether it has been queued for treatment and deletion */
  bool queued;
  /**
   * Identifier of where in the conflict_core this pair appears / originates from.
   * 0 is the identifier for the set of equalities in the conflict core (a set of pairs).
   * Then each disequality in the conflict core gets an identifier between 1 and n,
   * and becomes a disjunction (a set of pairs) when sliced. Hence, if appearing_in is
   * 0, then the equality (lhs=rhs) is one of the constraints to satisfy,
   * and if appearing_in is i (1 <= i <= n), then the disequality (lhs!=rhs)
   * is one of the disjuncts of the disjunction number i, which needs to be satisfied.
   */
  uint32_t appearing_in;
} spair_t;

typedef struct splist_s splist_t;

/**
 * List of pairs of slices.
 *
 * When a pair (lhs,rhs) is created, it will be added (as main) to lhs's
 * list of pairs, and (as non-main) to rhs's list of pairs.
 */
struct splist_s {
  spair_t* pair;
  bool is_main;
  splist_t* next;
};

/** Slices: variable (or constant term) + extraction indices
    We avoid building the term to avoid cluttering the world with slices that may be short-lived
    The slices for a given variable form a binary tree; the leaves are the thinnest slices 
 */

struct slice_s {
  /** Variable or constant term, from which the slice is extracted */
  term_t term;
  /** Value of the slice (computed at the end from the trail, and only for leaf slices) */
  mcsat_value_t value;
  /** Term expressing the slice (computed at the end from the trail, and only for leaf slices) */
  term_t slice_term;
  /** Low index */
  uint32_t lo;
  /** High index + 1 (that index is not in the slice), so that hi - low = slice length */
  uint32_t hi;
  /** sub-slice towards the high indices, hi_sub->hi is the same as hi */
  slice_t* hi_sub;
  /** sub-slice towards the low indices, lo_sub->lo is the same as lo, lo_sub->hi is the same as hi_sub->lo */
  slice_t* lo_sub;
  /**
   * Other slices that this slice should be equal to or different from, as a
   * list of pairs (this slice is one side of each pair).
   */
  splist_t* paired_with;
};

/* List of slices */
typedef struct slist_s slist_t;

struct slist_s {
  slice_t* slice;
  slist_t* next;
};
  
// Main slicing algorithm

/** Type for a slicing = what is returned from a conflict core by the main function below */
typedef struct {
  /** Context, for utilities */
  plugin_context_t* ctx;
  /**
   * Array of lists of pairs.
   * Cell 0 contains the list of slice equalities; then each cell contains a
   * list representing a disjunction of slice disequalities
   */
  splist_t** constraints;
  /** length of constraints */
  uint32_t nconstraints;
  /** Maps each involved variable (or constant term) to its slice-tree */
  ptr_hmap_t slices;
} bv_slicing_t;

/**
 * Main function.
 * Gets a conflict core, produces the coarsest slicing.
 * The resulting slicing is in slicing_out, which only needs to be allocated, as this function will take care of initialisation.
 */
void bv_slicing_construct(bv_slicing_t* slicing, plugin_context_t* ctx, const ivector_t* conflict_core, eq_graph_t* egraph);

/** Destructs a slicing. Everything goes. */
void bv_slicing_slicing_destruct(bv_slicing_t* slicing);

/** Print the slicing. */
void bv_slicing_print_slicing(const bv_slicing_t* slicing, FILE* out);

/** Prints slice */
void bv_slicing_print_slice(const bv_slicing_t* slicing, const slice_t* s, FILE* out);

/** Prints a pair. if b is true, as an equality, otherwise, as a disequality */
void bv_slicing_print_spair(const bv_slicing_t* slicing, spair_t* p, bool b, FILE* out);

/** Prints a list of pairs. if b is true, then these are equalities, otherwise, disequalities */
void bv_slicing_print_splist(const bv_slicing_t* slicing, splist_t* spl, bool b, FILE* out);

