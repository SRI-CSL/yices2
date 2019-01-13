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
    stacks on tail consecutive subslices of s that cover s (starting with low indices),
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


/** Stacks on argument tail consecutive subslices of s that cover s from lo to hi
    (starting with low indices). If either lo or hi does not coincide with an existing 
    slicepoint of s, they get created. None of the subslices of s should be paired yet.
 */
slist_t* bv_slicing_extracts(slice_t* s, uint32_t hi, uint32_t lo, slist_t* tail){

  if ((hi <= s->lo) || (lo >= s->hi)) return tail; // Slice is disjoint from indices

  // We split the slice if need be (has to be a leaf,
  // and either hi or lo (or both) has to be a splitting index
  if (s->lo_sub == NULL){ // This slice is a leaf
    assert(s->paired_with == NULL);
    slice_t* s0 = s;
    if ((s0->lo < hi) && (hi < s0->hi)){
      bv_slicing_slice(s0, hi, NULL); // We don't have a todo queue but it's ok
      s0 = s0->lo_sub;
    }
    if ((s0->lo < lo) && (lo < s0->hi))
      bv_slicing_slice(s0, lo, NULL); // We don't have a todo queue but it's ok
  }

  // Now we create the list to return
  if (s->lo_sub == NULL) // This slice is (still!) a leaf, we add it to the tail
    return bv_slicing_scons(s, tail);

  // Otherwise it has two children and we call ourselves recursively
  return bv_slicing_extracts(s->lo_sub, hi, lo, bv_slicing_extracts(s->hi_sub, hi, lo, tail));
}


/** Normalises the hi-lo extraction of a term into a list of slices added to tail,
    which acts as an accumulator for this recursive function.
 */
slist_t* bv_slicing_norm(plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_hmap_t* slices){

  // standard abbreviations
  variable_db_t* var_db = ctx->var_db;
  term_table_t*  terms  = ctx->terms;

  term_kind_t kind = term_kind(terms, t);
  switch (kind) {
  case BV_ARRAY: {
    // Special: make sub-terms positive (TODO: what are positive terms?)
    composite_term_t* concat_desc = bvarray_term_desc(terms, t); // concatenated bitvector terms
    // Variables that will evolve in the loop
    uint32_t width_i        = bv_term_bitsize(terms, t); // how many bits before the current element, initialised with the width of whole term
    slist_t* current        = tail;  // the list constructed so far
    uint32_t hi_i, lo_i;             // local window

    // we go through the concatenated bitvectors, starting from the end,
    // assuming that the end represents the high bits (TODO: check this)
    for (uint32_t i = concat_desc->arity - 1; i >= 0 ; --i) {
      term_t t_i = concat_desc->arg[i];
      // term_t t_i_pos = unsigned_term(t_i); TODO: What is that?
      width_i = width_i - bv_term_bitsize(terms, t_i);
      hi_i = (hi > width_i)?(hi - width_i):0;
      lo_i = (lo > width_i)?(lo - width_i):0;
      current = bv_slicing_norm(ctx, t_i, hi_i, lo_i, current, slices);
    }
    return current;
  }
  case BIT_TERM: // 1-bit select?
    // TODO
    // bit_term_arg(terms, t)
  case BV_EQ_ATOM: // TODO?
  case CONSTANT_TERM: // TODO?
  case BV_CONSTANT: // TODO?
  case BV64_CONSTANT: // TODO?
  default: {
    variable_t var = variable_db_get_variable(var_db, t);
    ptr_hmap_pair_t* p = ptr_hmap_get(slices, var);
    if (p->val == NULL) p->val = bv_slicing_slice_new(var, 0, bv_term_bitsize(terms, t));
    return bv_slicing_extracts(p->val, hi, lo, tail);
  }
  }

}

/** Pours matching pairs of leaves into an array of constraints */

void bv_slicing_constraints(slice_t* s, splist_t** constraints){
  if (s->lo_sub == NULL) { // This is a leaf
    spair_t* p;
    splist_t *current = s->paired_with;
    while (current != NULL) {
      if (current->is_main) {
        p = current->pair;
        uint32_t c = p->appearing_in;
        splist_t* old = constraints[c];
        constraints[c] = bv_slicing_spcons(p, true, old);
      }
      current = current->next;
    }
  }
  else {
    bv_slicing_constraints(s->lo_sub, constraints);
    bv_slicing_constraints(s->hi_sub, constraints);
  }
}



/** Main function.
    Gets a conflict core, produces the coarsest slicing.
    The way this output is to be communicated / returned
    has yet to be determined */
void bv_slicing(plugin_context_t* ctx, const ivector_t* conflict_core, variable_t conflict_var, slicing_t* slicing_out){

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
    safe_free(p);
  }

  // We destruct the todo queue
  assert(ptr_queue_is_empty(todo));
  delete_ptr_queue(todo);

  slicing_out->nconstraints = next_disjunction;
  slicing_out->constraints = safe_malloc(sizeof(splist_t*) * next_disjunction);
  
  ptr_hmap_pair_t* hp = ptr_hmap_first_record(&slicing_out->slices);
  while(hp != NULL) {
    bv_slicing_constraints(hp->val, slicing_out->constraints);
    hp = ptr_hmap_next_record(&slicing_out->slices, hp);
  }
  
}
