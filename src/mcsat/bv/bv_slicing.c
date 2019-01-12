/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/variable_db.h"
#include "mcsat/tracing.h"

#include "bv_utils.h"
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


/** Refines slice tree s to make sure there are slice points at indices hi and lo. None of the slices in the tree should be paired yet. */
void bv_slicing_refines(slice_t s, uint32_t hi, uint32_t lo){
  // TODO
  return;
}


/** Normalises a term into a list of slices added to tail,
    which acts as an accumulator for this recursive function.
    The head of the output list will necessarily be a leaf slice.
 */
slist_t* bv_slicing_norm(const plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_hmap_t* slices){
  // TODO
  return NULL;
}

/** Main function.
    Gets a conflict core, produces the coarsest slicing.
    The way this output is to be communicated / returned
    has yet to be determined */
void bv_slicing(const plugin_context_t* ctx, const ivector_t* conflict_core, variable_t conflict_var, slicing_t* slicing_out){

  // standard abbreviations
  const variable_db_t* var_db = ctx->var_db;
  const term_table_t*  terms  = ctx->terms;
  const mcsat_trail_t* trail  = ctx->trail;

  // We create a "to do" queue of matching slice pairs to align
  ptr_queue_t* todo = safe_malloc(sizeof(ptr_queue_t));
  init_ptr_queue(todo, 0);
 
  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;
  composite_term_t* atom_i_comp;
  term_kind_t atom_i_kind;
    
  // Counter that records the next available identifier to assign to a disequality in the core.
  // That disequality turns into a disjunction when slicing 
  uint32_t next_disjunction = 1;

  for (uint32_t i = 0; i < conflict_core->size; i++) {
    atom_i_var   = conflict_core->data[i];
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    atom_i_term  = variable_db_get_term(var_db, atom_i_var);
    atom_i_kind  = term_kind(terms, atom_i_term);
    switch (atom_i_kind) {
    case EQ_TERM: { // We can only deal with equalities in this BV subtheory
      atom_i_comp = composite_term_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      uint32_t constraint = 0;
      if (!atom_i_value) {
        constraint = next_disjunction;
        next_disjunction++;
      }
      uint32_t width = bv_term_bitsize(terms, t0);
      slist_t* l0 = bv_slicing_norm(ctx, t0, width, 0, NULL, &slicing_out->slices);
      slist_t* l1 = bv_slicing_norm(ctx, t1, width, 0, NULL, &slicing_out->slices);
      bv_slicing_align(l0, l1, constraint, todo);      
      break;
    }
    default:
      assert(false);
    }
  }

  /** While loop treating the queue of slicings to perform until the coarsest slicing has been produced */
  spair_t* p;
  slist_t* l1;
  slist_t* l2;
  
  while (!ptr_queue_is_empty(todo)){
    p = (spair_t*) ptr_queue_pop(todo);
    l1 = bv_slicing_as_list(p->lhs, NULL);
    l2 = bv_slicing_as_list(p->rhs, NULL);
    bv_slicing_align(l1, l2, p->appearing_in, todo); // l1 and l2 are freed
  }

  // We destruct the todo queue
  assert(ptr_queue_is_empty(todo));
  delete_ptr_queue(todo);
}
