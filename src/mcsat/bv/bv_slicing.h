/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#pragma once


#include "mcsat/tracing.h"
#include "mcsat/mcsat_types.h"

#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"

#include "utils/ptr_queues.h"
#include "utils/ptr_hash_map.h"

/* #include <inttypes.h> useful? */

typedef struct slice_s slice_t;

/* Pair of slices (equality or disequality) */
typedef struct {
  slice_t* lhs;
  slice_t* rhs;
  bool queued; // whether it has been queued for treatment and deletion
  /** Identifier of where in the conflict_core this pair appears / originates from.
      0 is the identifier for the set of equalities in the conflict core (a set of pairs)
      Then each disequality in the conflict core gets an identifier between 1 and n,
      and becomes a disjunction (a set of pairs) when sliced.
      Hence, if appearing_in is 0, then the equality (lhs=rhs) is one of the constraints to satisfy,
      and if appearing_in is i (1 <= i <= n), then the disequality (lhs!=rhs) is one of the disjuncts of the disjunction number i, which needs to be satisfied.
 */
  uint32_t appearing_in;
} spair_t;


/* List of pairs of slices */

typedef struct splist_s splist_t;

struct splist_s {
  spair_t* pair;
  bool is_main; // when a pair (lhs,rhs) is created, it will be added (as main) to lhs's list of pairs, and (as non-main) to rhs's list of pairs
  splist_t* next;
};

/** Slices: variable (or constant term) + extraction indices
    We avoid building the term to avoid cluttering the world with slices that may be short-lived
    The slices for a given variable form a binary tree; the leaves are the thinnest slices 
 */

struct slice_s {
  /** Variable or constant term */
  term_t term;
  /** Low index */
  uint32_t lo;
  /** High index + 1 (that index is not in the slice), so that hi - low = slice length */
  uint32_t hi;
  /** sub-slice towards the high indices, hi_sub->hi is the same as hi */
  slice_t* hi_sub;
  /** sub-slice towards the low indices, lo_sub->lo is the same as lo, lo_sub->hi is the same as hi_sub->lo */
  slice_t* lo_sub;
  /** Other slices that this slice should be equal to or different from,
      as a list of pairs (this slice is one side of each pair) */
  splist_t* paired_with;
};

/* List of slices */

typedef struct slist_s slist_t;

struct slist_s {
  slice_t* slice;
  slist_t* next;
};



// Create term from slice
term_t bv_slicing_slice2term(const slice_t* s, plugin_context_t* ctx);

  
// Printing

/** Prints slice */
void bv_slicing_print_slice(const slice_t* s, term_table_t* terms, FILE* out);

/** Prints a pair. if b is true, as an equality, otherwise, as a disequality */

void bv_slicing_print_spair(spair_t* p, bool b, term_table_t* terms, FILE* out);

/** Prints a list of pairs. if b is true, then these are equalities, otherwise, disequalities */

void bv_slicing_print_splist(splist_t* spl, bool b, term_table_t* terms, FILE* out);


// Main slicing algorithm

/** Type for a slicing = what is returned from a conflict core by the main function below */

typedef struct {
  splist_t** constraints; // array of lists of pairs: cell 0 contains the list of slice equalities; then each cell contains a list representing a disjunction of slice disequalities
  uint32_t nconstraints; // length of constraints
  ptr_hmap_t slices;     // Maps each involved variable (or constant term) to its slice-tree
} slicing_t;

// Prints a slicing.
void bv_slicing_print_slicing(slicing_t* slicing, term_table_t* terms, FILE* out);

// Destructs a slicing. Everything goes.
void bv_slicing_slicing_destruct(slicing_t* slicing);


/** Main function.
    Gets a conflict core, produces the coarsest slicing.
    The resulting slicing is in slicing_out, which only needs to be allocated, as this function will take care of initialisation.
 */
void bv_slicing_construct(plugin_context_t* ctx, const ivector_t* conflict_core, slicing_t* slicing_out);
