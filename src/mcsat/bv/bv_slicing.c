/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/variable_db.h"
#include "mcsat/tracing.h"

#include "bv_slicing.h"

/** pair construct */
spair_t* bv_slicing_spair_new(slice_t* lhs, slice_t* rhs, uint32_t appearing_in){

  spair_t* pair = safe_malloc(sizeof(spair_t));
  pair->lhs = lhs;
  pair->rhs = rhs;
  pair->appearing_in = appearing_in;
  return pair;
  
}

/** splist cons */
splist_t* bv_slicing_spcons(spair_t* pair, bool is_main, splist_t* tail){

  splist_t* result = safe_malloc(sizeof(splist_t));
  result->pair = pair;
  result->is_main = is_main;
  result->next = tail;
  return result;
}

void bv_slicing_print_slice(const variable_db_t* var_db, const slice_t* s, FILE* out) {
  variable_db_print_variable(var_db, s->var, out);
  fprintf(out, "[");
  fprintf(out, "%i", (s->hi)-1);
  fprintf(out, ":");
  fprintf(out, "%i", s->lo);
  fprintf(out, "]");
}


/** Creates a leaf slice, no children */
slice_t* bv_slicing_slice_new(variable_t var, uint32_t lo, uint32_t hi){

  assert(lo < hi);
  slice_t* result = safe_malloc(sizeof(slice_t));

  result->var = var;
  result->lo  = lo;
  result->hi  = hi;
  result->paired_with = NULL;
  result->lo_sub  = NULL;
  result->hi_sub  = NULL;

  return result;
}

/** Deletes a slice, recursively deleting children if they exist.
    Also deletes the pairs involving the slice along the way.
 */
void bv_slicing_slice_delete(slice_t* s){
  if (s->lo_sub != NULL) bv_slicing_slice_delete(s->lo_sub);
  if (s->hi_sub != NULL) bv_slicing_slice_delete(s->hi_sub);
  splist_t *b = s->paired_with;
  splist_t *next;

  while (b != NULL) {
    next = b->next;
    safe_free(b);
    b = next;
  }
  safe_free(s);
}

/** slist cons */
slist_t* bv_slicing_scons(slice_t* s, slist_t* tail){

  slist_t* result = safe_malloc(sizeof(slist_t));
  result->slice = s;
  result->next = tail;
  return result;
}


/** Slices slice s at index k, pushing resulting slicings to be performed in the "todo" queue */
void bv_slicing_slice(slice_t* s, uint32_t k, ptr_queue_t* todo){
  assert(s->lo_sub == NULL);
  assert(s->hi_sub == NULL);
  assert(k < s->hi);
  assert(s->lo < k);
  s->lo_sub  = bv_slicing_slice_new(s->var, s->lo, k);
  s->hi_sub  = bv_slicing_slice_new(s->var, k, s->hi);

  splist_t *b = s->paired_with;
  splist_t *next;

  while (b != NULL) {
    ptr_queue_push(todo, b->pair);
    next = b->next;
    safe_free(b);
    b = next;
  }
  s->paired_with = NULL;
}

/** From a slice s and a stack of slices tail,
    stacks on tail consecutive subslices of s that cover s,
    with the property that the first one is a leaf slice.
    recursive function with tail being an accumulator. */
slist_t* bv_slicing_as_list(slice_t* s, slist_t* tail){
  assert(s != NULL);
  if (s->hi_sub == NULL) return bv_slicing_scons(s,tail);
  return bv_slicing_as_list(s->lo_sub, bv_slicing_scons(s->hi_sub, tail));
}

/** Aligns 2 series l1 and l2 of slices, producing matching pairs (s1,s2) where s1 and s2 have equal length.
    The alignment can trigger some future slicings that are queued in todo.
    Destructs l1 and l2 along the way.
 */
void bv_slicing_align(slist_t* l1, slist_t* l2, uint32_t appearing_in, ptr_queue_t* todo){
  slice_t* h1 = l1->slice;
  slice_t* h2 = l2->slice;
  slist_t* t1 = l1->next;
  slist_t* t2 = l2->next;
  uint32_t w1 = h1->hi - h1->lo;
  uint32_t w2 = h2->hi - h2->lo;
  if ( w1 < w2 ){
    // h1 is shorter than h2; we need to slice h2
    safe_free(l2); // We are not going to re-use l2
    bv_slicing_slice(h2, h2->lo + w1, todo); // We slice h2
    return bv_slicing_align(l1, bv_slicing_as_list(h2,t2), appearing_in, todo);
  }
  if ( w2 < w1 ){
    // h2 is shorter than h1; we need to slice h1
    safe_free(l1); // We are not going to re-use l1
    bv_slicing_slice(h1, h1->lo + w2, todo); // We slice h2
    return bv_slicing_align(bv_slicing_as_list(h1,t1), l2, appearing_in, todo);
  }
  // OK, h1 and h2 have the same width; we can pair them.
  // We no longer need l1 and l2
  safe_free(l1);
  safe_free(l2);
  spair_t* p = bv_slicing_spair_new(h1, h2, appearing_in); // We form the pair
  h1->paired_with = bv_slicing_spcons(p, true, h1->paired_with);
  h2->paired_with = bv_slicing_spcons(p, false, h2->paired_with);
  bv_slicing_align(t1, t2, appearing_in, todo);
}

/** While loop treating the queue of slicings to perform until the coarsest slicing has been produced */
void bv_slicing_treat(ptr_queue_t* todo){

  spair_t* p;
  slist_t* l1;
  slist_t* l2;
  
  while (!ptr_queue_is_empty(todo)){
    p = (spair_t*) ptr_queue_pop(todo);
    l1 = bv_slicing_as_list(p->lhs, NULL);
    l2 = bv_slicing_as_list(p->rhs, NULL);
    bv_slicing_align(l1, l2, p->appearing_in, todo); // l1 and l2 are freed
  }

}
