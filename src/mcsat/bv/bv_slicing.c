/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/variable_db.h"
#include "mcsat/tracing.h"

#include "bv_slicing.h"

void bv_slicing_print_slice(const variable_db_t* var_db, const slice_t* s, FILE* out) {
  variable_db_print_variable(var_db, s->var, out);
  fprintf(out, "[");
  fprintf(out, "%i\n", (s->hi)-1);
  fprintf(out, ":");
  fprintf(out, "%i\n", s->lo);
  fprintf(out, "]");
}


/** Construct a leaf slice, no children */
void bv_slicing_slice_construct(slice_t* slice, variable_t var, uint32_t lo, uint32_t hi){
  return;
}

/** Destruct a slice, which recursively destructs children if they exist */
void bv_slicing_slice_destruct(slice_t* slice){
  return;
}

/** Construct a pair */
pair_t* bv_slicing_pair_construct(slice_t* lhs, slice_t* rhs, int_bag_t* appearing_in){

}

/** Destruct a pair (does not destruct appearing_in field) */
void bv_slicing_pair_destruct(pair_t* p){

}



/** Slices slice s at index k, pushing resulting slicings to be performed in the "todo" queue */
void bv_slicing_slice(slice_t* s, uint32_t k, ptr_queue_t* todo){

}

/** From a slice s and a stack of slices tail,
    stacks on tail consecutive subslices of s that cover s,
    with the property that the first one is a leaf slice.
    recursive function with tail being an accumulator. */
ptr_stack_t* bv_slicing_as_list(slice_t* s, ptr_stack_t* tail){

}

/** Aligns 2 series l1 and l2 of slices, producing matching pairs (s1,s2) where s1 and s2 have equal length.
    The alignment can trigger some future slicings that are queued in todo.
    Destructs l1 and l2 along the way.
 */
void bv_slicing_align(ptr_stack_t* l1, ptr_stack_t* l2, ptr_queue_t* todo){

}

/** While loop treating the queue of slicings to perform until the coarsest slicing has been produced */
void bv_slicing_treat(ptr_queue_t* todo){

}
