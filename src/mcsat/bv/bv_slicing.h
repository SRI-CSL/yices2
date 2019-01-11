/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#pragma once

#include "mcsat/mcsat_types.h"

#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"
#include "terms/term_manager.h"

#include "utils/ptr_stack.h"
#include "utils/ptr_queues.h"
#include "utils/ptr_hash_map.h"
#include "utils/int_bags.h"

/* #include <inttypes.h> useful? */

/** Slices: variable + extraction indices
    We avoid building the term to avoid cluttering the world with slices that may be short-lived
    The slices for a given variable form a binary tree; the leaves are the thinnest slices 
 */

typedef struct slice_s slice_t;

struct slice_s {
  /** Variable */
  variable_t var;
  /** Low index */
  uint32_t lo;
  /** High index + 1 (that index is not in the slice), so that hi - low = slice length */
  uint32_t hi;
  /** sub-slice towards the high indices, hi_sub->hi is the same as hi */
  slice_t* hi_sub;
  /** sub-slice towards the low indices, lo_sub->lo is the same as lo, , lo_sub->hi is the same as hi_sub->lo */
  slice_t* lo_sub;
  /** Other slices that this slice should be equal to or different from, as a hash_map
      from the other slice to the pair containing the two slices (see pair_t below) */
  ptr_hmap_t paired_with;
};

typedef struct {
  /** Left-hand side */
  slice_t* lhs;
  /** Right-hand side */
  slice_t* rhs;
  /** Set of identifiers:
      0 is the identifier for the set of equalities in the conflict core (a set of pairs)
      Then each disequality in the conflict core gets an identifier between 1 and n,
      and becomes a disjunction (a set of pairs) when sliced.
      Hence, if appearing_in contains 0, then the equality (lhs=rhs) is one of the constraints to satisfy,
      and if appearing_in contains i (1 <= i <= n), then the disequality (lhs!=rhs) is one of the disjuncts of the disjunction number i, which needs to be satisfied.
 */
  int_bag_t* appearing_in;
} pair_t;


/** Prints slice (does not show subslices) */
void bv_slicing_print_slice(const variable_db_t* var_db, const slice_t* s, FILE* out);

/** Construct a leaf slice, no children */
void bv_slicing_slice_construct(slice_t* slice, variable_t var, uint32_t lo, uint32_t hi);

/** Destruct a slice, which recursively destructs children if they exist */
void bv_slicing_slice_destruct(slice_t* slice);

/** Construct a pair */
pair_t* bv_slicing_pair_construct(slice_t* lhs, slice_t* rhs, int_bag_t* appearing_in);

/** Destruct a pair (does not destruct appearing_in field) */
void bv_slicing_pair_destruct(pair_t* p);



/** Slices slice s at index k, pushing resulting slicings to be performed in the "todo" queue */
void bv_slicing_slice(slice_t* s, uint32_t k, ptr_queue_t* todo);

/** From a slice s and a stack of slices tail,
    stacks on tail consecutive subslices of s that cover s,
    with the property that the first one is a leaf slice.
    recursive function with tail being an accumulator. */
ptr_stack_t* bv_slicing_as_list(slice_t* s, ptr_stack_t* tail);


/** Aligns 2 series l1 and l2 of slices, producing matching pairs (s1,s2) where s1 and s2 have equal length.
    The alignment can trigger some future slicings that are queued in todo.
    Destructs l1 and l2 along the way.
 */
void bv_slicing_align(ptr_stack_t* l1, ptr_stack_t* l2, ptr_queue_t* todo);

/** While loop treating the queue of slicings to perform until the coarsest slicing has been produced */
void bv_slicing_treat(ptr_queue_t* todo);
