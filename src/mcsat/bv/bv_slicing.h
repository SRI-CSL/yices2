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
#include "terms/term_manager.h"

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

/** Slices: variable + extraction indices
    We avoid building the term to avoid cluttering the world with slices that may be short-lived
    The slices for a given variable form a binary tree; the leaves are the thinnest slices 
 */

struct slice_s {
  /** Variable */
  variable_t var;
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


// Pairs and lists thereof

/** pair construct */
spair_t* bv_slicing_spair_new(slice_t* lhs, slice_t* rhs, uint32_t appearing_in);

/** splist cons */
splist_t* bv_slicing_spcons(spair_t* p, bool is_main, splist_t* tail);

/** delete a list of pairs, also deleting each pair if b == true.
    In any case, not deleting slices that pairs consist of. */
void bv_slicing_spdelete(splist_t* spl, bool b);



// Slices themselves

/** Prints slice */
void bv_slicing_print_slice(const variable_db_t* var_db, const slice_t* s, FILE* out);

/** Creates a leaf slice, no children */
slice_t* bv_slicing_slice_new(variable_t var, uint32_t lo, uint32_t hi);

/** Deletes a slice, recursively deleting children if they exist.
    Also deletes the list of pairs involving the slice along the way, but not deleting the pairs themselves. */
void bv_slicing_slice_delete(slice_t* slice);

/** slist cons */
slist_t* bv_slicing_scons(slice_t* s, slist_t* tail);



// Slice splitting and basic alignment

/** Slices slice s at index k, pushing resulting slicings to be performed in the "todo" queue */
void bv_slicing_slice(slice_t* s, uint32_t k, ptr_queue_t* todo, const variable_db_t* var_db, FILE* out);

/** From a slice s and a stack of slices tail,
    stacks on the tail consecutive subslices of s that cover s,
    with the property that the first one is a leaf slice.
    recursive function with tail being an accumulator. */
slist_t* bv_slicing_as_list(slice_t* s, slist_t* tail);

/** Aligns 2 series l1 and l2 of slices, producing matching pairs (s1,s2) where s1 and s2 have equal length.
    The alignment can trigger some future slicings that are queued in todo.
    Destructs l1 and l2 along the way. */
void bv_slicing_align(slist_t* l1, slist_t* l2, uint32_t appearing_in, ptr_queue_t* todo, const variable_db_t* var_db, FILE* out);



// Normalising actual bitvector terms into list of slices

/** Stacks on argument tail consecutive subslices of s that cover s from lo to hi
    (head of result is the lowest index slice). If either lo or hi does not coincide with an existing 
    slicepoint of s, they get created. None of the subslices of s should be paired yet. */
slist_t* bv_slicing_extracts(slice_t* s, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, const variable_db_t* var_db, FILE* out);

/** Wrapping up above function: stack on top of tail a slice for variable t (expressed as a term), from lo to hi */
slist_t* bv_slicing_sstack(plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices);

/** Normalises a term into a list of slices added to tail,
    which acts as an accumulator for this recursive function.
    The head of the output list will necessarily be a leaf slice.
 */
slist_t* bv_slicing_norm(plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices);


// Main slicing algorithm

/** Type for a slicing = what is returned from a conflict core by the main function below */

typedef struct {
  splist_t** constraints; // array of lists of pairs: cell 0 contains the list of slice equalities; then each cell contains a list representing a disjunction of slice disequalities
  uint32_t nconstraints; // length of constraints
  ptr_hmap_t slices;     // Maps each involved variable to its slice-tree
} slicing_t;

// Prints a slicing.
void bv_slicing_print_slicing(const variable_db_t* var_db, slicing_t* slicing, FILE* out);

  // Destructs a slicing. Everything goes.
void bv_slicing_slicing_destruct(slicing_t* slicing);

/** Pours matching pairs of leaves into an array of constraints */

void bv_slicing_constraints(slice_t* s, splist_t** constraints);

/** Main function.
    Gets a conflict core, produces the coarsest slicing.
    The resulting slicing is in slicing_out, which only needs to be allocated, as this function will take care of initialisation.
 */
void bv_slicing_construct(plugin_context_t* ctx, const ivector_t* conflict_core, variable_t conflict_var, slicing_t* slicing_out);
