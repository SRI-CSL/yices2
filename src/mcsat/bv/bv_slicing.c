/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/tracing.h"
#include "terms/term_manager.h"
#include "terms/bvlogic_buffers.h"

#include "bv_utils.h"
#include "bv_slicing.h"

/** pair construct */
spair_t* bv_slicing_spair_new(slice_t* lhs, slice_t* rhs, uint32_t appearing_in){
  assert(lhs != NULL);
  assert(rhs != NULL);
  spair_t* pair = safe_malloc(sizeof(spair_t));
  pair->lhs = lhs;
  pair->rhs = rhs;
  pair->queued = false;
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

/** delete a list of pairs, also deleting each pair if b == true.
    In any case, not deleting slices that pairs consist of. */
void bv_slicing_spdelete(splist_t* spl, bool b){
  splist_t* l = spl;
  splist_t* next;
  while (l != NULL) {
    next = l->next;
    if (b) safe_free(l->pair);
    safe_free(l);
    l = next;
  }
}

// Create term from slice
term_t bv_slicing_slice2term(const slice_t* s, plugin_context_t* ctx) {
  assert(s->lo_sub == NULL);
  term_manager_t* tm = &ctx->var_db->tm;
  bvlogic_buffer_t* buffer = term_manager_get_bvlogic_buffer(tm);
  bvlogic_buffer_set_slice_term(buffer, ctx->terms, s->lo, s->hi-1, s->term);
  term_t result = mk_bvlogic_term(tm, buffer);
  return result;
}

// PRINTING

/** Prints slice */

void bv_slicing_print_slice_aux(const slice_t* s, FILE* out) {
  fprintf(out, "[");
  if (s->lo_sub != NULL) {
    bv_slicing_print_slice_aux(s->hi_sub, out);
    bv_slicing_print_slice_aux(s->lo_sub, out);
  }
  else {
    if ((s->hi) == (s->lo)+1) fprintf(out, "%i", s->lo);
    else fprintf(out, "%i:%i", (s->hi)-1, s->lo);
  }
  fprintf(out, "]");
}

void bv_slicing_print_slice(const slice_t* s, term_table_t* terms, FILE* out) {
  term_print_to_file(out, terms, s->term);
  bv_slicing_print_slice_aux(s, out);
}

/** Prints a list of slices. */

void bv_slicing_print_slist(slist_t* sl, term_table_t* terms, FILE* out){
  slist_t* l = sl;
  while (l != NULL) {
    bv_slicing_print_slice(l->slice, terms, out);
    l = l->next;
    if (l != NULL) fprintf(out, "::");
  }
}

/** Prints a pairs. if b is true, as an equality, otherwise, as a disequality */

void bv_slicing_print_spair(spair_t* p, bool b, term_table_t* terms, FILE* out){
  assert(p->lhs != NULL);
  assert(p->rhs != NULL);
  bv_slicing_print_slice(p->lhs, terms, out);
  fprintf(out, "%s", b?"=":"≠");
  bv_slicing_print_slice(p->rhs, terms, out);
}

/** Prints a list of pairs. if b is true, then these are equalities, otherwise, disequalities */

void bv_slicing_print_splist(splist_t* spl, bool b, term_table_t* terms, FILE* out){
  splist_t* l = spl;
  while (l != NULL) {
    bv_slicing_print_spair(l->pair, b, terms, out);
    l = l->next;
    if (l != NULL) fprintf(out, "%s", b?" ∧ ":" ∨ ");
  }
}


/** Creates a leaf slice, no children */
slice_t* bv_slicing_slice_new(term_t term, uint32_t lo, uint32_t hi){

  assert(lo < hi);
  slice_t* result = safe_malloc(sizeof(slice_t));

  result->term = term;
  result->lo  = lo;
  result->hi  = hi;
  result->paired_with = NULL;
  result->lo_sub  = NULL;
  result->hi_sub  = NULL;

  return result;
}

/** Deletes a slice, recursively deleting children if they exist.
    Also deletes the list of pairs involving the slice along the way, but not deleting the pairs themselves. */
void bv_slicing_slice_delete(slice_t* s){
  if (s->lo_sub != NULL) bv_slicing_slice_delete(s->lo_sub);
  if (s->hi_sub != NULL) bv_slicing_slice_delete(s->hi_sub);
  bv_slicing_spdelete(s->paired_with, false);
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
void bv_slicing_slice(slice_t* s, uint32_t k, ptr_queue_t* todo, term_table_t* terms, FILE* out){

  /* fprintf(out, "Slicing "); */
  /* bv_slicing_print_slice(s, terms, out); */
  /* fprintf(out, " at %d\n", k); */

  assert(s->lo_sub == NULL);
  assert(s->hi_sub == NULL);
  assert(k < s->hi);
  assert(s->lo < k);
  s->lo_sub  = bv_slicing_slice_new(s->term, s->lo, k);
  s->hi_sub  = bv_slicing_slice_new(s->term, k, s->hi);

  splist_t *b = s->paired_with;
  splist_t *next;

  while (b != NULL) {
    spair_t* p = b->pair;
    /* fprintf(out, "Queueing "); */
    /* bv_slicing_print_spair(p, true, terms, out); */
    /* fprintf(out, "\n"); */
    if (!p->queued) {
      p->queued = true;
      ptr_queue_push(todo, p);
    }
    next = b->next;
    safe_free(b); // We delete the list nodes along the way (but not the pairs themselves)
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
void bv_slicing_align(slist_t* l1, slist_t* l2, uint32_t appearing_in, ptr_queue_t* todo, term_table_t* terms, FILE* out){

  /* fprintf(out,"Aligning "); */
  /* bv_slicing_print_slist(l1, terms, out); */
  /* fprintf(out," with "); */
  /* bv_slicing_print_slist(l2, terms, out); */
  /* fprintf(out,"\n"); */
    
  if (l1 == NULL) return; // Reached the end of the lists. We stop.
  assert(l2 != NULL);     // If l1 not empty then l2 not empty as the two lists must have the same total bitsize
  slice_t* h1 = l1->slice;
  slice_t* h2 = l2->slice;
  slist_t* t1 = l1->next;
  slist_t* t2 = l2->next;
  uint32_t w1 = h1->hi - h1->lo;
  uint32_t w2 = h2->hi - h2->lo;

  if ((h1->lo_sub == NULL) && (h2->lo_sub == NULL)) { // if both h1 and h2 are leaves
    if ( w1 < w2 ) // h1 is shorter than h2, we slice h2
      bv_slicing_slice(h2, h2->lo + w1, todo, terms, out); // We slice h2
    if ( w2 < w1 ) // h2 is shorter than h1, we slice h1
      bv_slicing_slice(h1, h1->lo + w2, todo, terms, out); // We slice h2
  }

  if (h2->lo_sub != NULL) { // head of l2 is not a leaf
    safe_free(l2); // l2 is not good, we free the node and recompute the list
    return bv_slicing_align(l1, bv_slicing_as_list(h2,t2), appearing_in, todo, terms, out);
  }

  if (h1->lo_sub != NULL) { // head of l1 is not a leaf
    safe_free(l1); // l1 is not good, we free the node and recompute the list
    return bv_slicing_align(bv_slicing_as_list(h1,t1), l2, appearing_in, todo, terms, out);
  }

  // OK, h1 and h2 have the same width; we can pair them.
  // We no longer need l1 and l2
  safe_free(l1);
  safe_free(l2);
  spair_t* p = bv_slicing_spair_new(h1, h2, appearing_in); // We form the pair

  /* fprintf(out,"Forming pair "); */
  /* bv_slicing_print_spair(p, true, terms, out); */
  /* fprintf(out,"\n"); */

  h1->paired_with = bv_slicing_spcons(p, true, h1->paired_with);
  h2->paired_with = bv_slicing_spcons(p, false, h2->paired_with);
  bv_slicing_align(t1, t2, appearing_in, todo, terms, out);
}


/** Stacks on argument tail consecutive subslices of s that cover s from lo to hi
    (head of result is the lowest index slice). If either lo or hi does not coincide with an existing 
    slicepoint of s, they get created. */
slist_t* bv_slicing_extracts(slice_t* s, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, term_table_t* terms, FILE* out){

  /* fprintf(out, "Extracts %d to %d from ", hi, lo); */
  /* bv_slicing_print_slice(s, terms, out); */
  /* fprintf(out, "\n"); */
  if ((hi <= s->lo) || (lo >= s->hi)) return tail; // Slice is disjoint from indices

  // We split the slice if need be (has to be a leaf,
  // and either hi or lo (or both) has to be a splitting index
  if (s->lo_sub == NULL){ // This slice is a leaf
    slice_t* s0 = s;
    if ((s0->lo < hi) && (hi < s0->hi)){
      bv_slicing_slice(s0, hi, todo, terms, out);
      /* fprintf(out, "splitting at hi=%d, giving ", hi); */
      /* bv_slicing_print_slice(s, terms, out); */
      /* fprintf(out, "\n"); */
      s0 = s0->lo_sub;
    }
    if ((s0->lo < lo) && (lo < s0->hi)){
      bv_slicing_slice(s0, lo, todo, terms, out);
      /* fprintf(out, "splitting at lo=%d, giving ", lo); */
      /* bv_slicing_print_slice(s, terms, out); */
      /* fprintf(out, "\n"); */
    }
  }

  // Now we create the list to return
  if (s->lo_sub == NULL) {// This slice is (still!) a leaf, we add it to the tail
    slist_t* result = bv_slicing_scons(s, tail);
    /* fprintf(out, "Extract returns "); */
    /* bv_slicing_print_slist(result, terms, out); */
    /* fprintf(out, "\n"); */
    return result;
  }


  slist_t* result = bv_slicing_extracts(s->lo_sub, hi, lo, bv_slicing_extracts(s->hi_sub, hi, lo, tail, todo, terms, out), todo, terms, out);

  /* fprintf(out, "Extract returns "); */
  /* bv_slicing_print_slist(result, terms, out); */
  /* fprintf(out, "\n"); */

  // Otherwise it has two children and we call ourselves recursively
  return result;
}


/** Wrapping up above function: stack on top of tail a slice for variable t (expressed as a term), from lo to hi */
slist_t* bv_slicing_sstack(plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices){

  FILE* out = ctx_trace_out(ctx);

  ptr_hmap_pair_t* p = ptr_hmap_get(slices, t);       // Getting that variable's top-level slice from global hashmap
  if (p->val == NULL) p->val = bv_slicing_slice_new(t, 0, bv_term_bitsize(ctx->terms, t)); // Create that slice if need be
  return bv_slicing_extracts(p->val, hi, lo, tail, todo, ctx->terms, out);     // stack upon the tail list the relevant (series of) slice(s) covering lo to hi
}

slist_t* bv_slicing_slice_close(plugin_context_t* ctx,
                              term_t* tp,
                              uint32_t bitwidth,
                              slist_t* tail,
                              ptr_queue_t* todo,
                              ptr_hmap_t* slices){


  /* FILE* out = ctx_trace_out(ctx); */
  /* fprintf(out, "Closing slice of width %d\n",bitwidth); */

  if (bitwidth == 0) return tail;
  term_table_t* terms = ctx->terms; // standard abbreviation
  term_t t0 = tp[0];

  switch (term_kind(terms, t0)) {

  case BIT_TERM: {
    select_term_t* desc   = bit_term_desc(terms, t0);
    term_t tvar           = desc->arg; // Get term variable
    uint32_t selected_bit = desc->idx; // Get bit that is selected in it
    return bv_slicing_sstack(ctx, tvar, selected_bit + bitwidth, selected_bit, tail, todo, slices);
  }

  case CONSTANT_TERM : {
    term_manager_t* tm = &ctx->var_db->tm;
    /* term_t cst = bvarray_term(terms, bitwidth, tp); // Primitive construction */
    term_t cst = mk_bvarray(tm, bitwidth, tp); // Smarter construction?
    return bv_slicing_sstack(ctx, cst, bitwidth, 0, tail, todo, slices);
  }

  default:
    assert(false);
  }
}


/** Normalises the hi-lo extraction of a term into a list of slices added to tail,
    which acts as an accumulator for this recursive function. */
slist_t* bv_slicing_norm(plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices){

  /* FILE* out = ctx_trace_out(ctx); */
  /* fprintf(out, "Normalising "); */
  /* term_print_to_file(out, ctx->terms, t); */
  /* fprintf(out, " between %d and %d\n", hi, lo); */

  assert(lo < hi);
  term_table_t* terms = ctx->terms; // standard abbreviation

  switch (term_kind(terms, t)) {
  case BV_ARRAY: {
    // Concatenated boolean terms:
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    assert(hi <= concat_desc->arity);
    /* fprintf(out, "This is a bv_array, where\n"); */

    // We go through the bits of the bv_array, starting from the end,
    // which represents the high bits.
    uint32_t total_width = hi - lo;
    
    // Variables that will evolve in the loop:
    slist_t* current = tail;  // the list constructed so far
    uint32_t width   = 0;     // bitwidth of current slice under construction
    bool     is_constant = true; // whether current slice is constant
    term_t   tvar;            // if not constant, variable term of current slice
    uint32_t low;             // if not constant, lo of current slice
    
    for (uint32_t j = 0; j < total_width ; j++) {
      uint32_t i = hi - j -1;           // The bit we are dealing with
      term_t t_i = concat_desc->arg[i]; // The Boolean term that constitutes that bit
      /* fprintf(out, "bit %d is ",i); */
      /* ctx_trace_term(ctx, t_i); */

      switch (term_kind(terms, t_i)) { // We look at what it is

      case BIT_TERM: {
        select_term_t* desc   = bit_term_desc(terms, t_i);
        term_t tmp            = desc->arg; // Get term variable
        uint32_t selected_bit = desc->idx; // Get bit that is selected in it
        // We need to change slice if...
        if (is_constant                   // ...the current slice was constant
            || (tmp != tvar)              // or it wasn't but it had different variable
            || (selected_bit + 1 != low)) // or it was the same but new bit not in continuity
          { // We close the current slice, stack it upon the tail, and open a new slice
            current = bv_slicing_slice_close(ctx, concat_desc->arg + i + 1,width, current, todo, slices);
            width = 0; // We start a new slice
          }
        // Then in any case:
        width++;                    // bitwidth of current slice is incremented
        is_constant = false;        // current slice is not constant
        tvar        = tmp;          // current slice has tvar as variable (as a term)
        low         = selected_bit; // ...and selected_bit as its low index
        break;
      }
      case CONSTANT_TERM: { // or it's a boolean constant true or false
        // We need to change slice if current slice was not constant
        if (!is_constant) {
          current = bv_slicing_slice_close(ctx, concat_desc->arg + i + 1,width, current, todo, slices);
          width = 0; // We start a new slice
        }
        // Then in any case:
        width++;            // bitwidth of current slice is incremented
        is_constant = true; // current slice is constant
        break;
      }
      default: // It can be nothing else
        assert(false);
      }
    }
    // We have exited the loop, we now close the current (and last) slice
    return bv_slicing_slice_close(ctx, concat_desc->arg,width, current, todo, slices);
  }
  case BIT_TERM: { // Term t is the selection of some bit from some variable
    assert(hi ==1); // The whole term being of bitwidth 1, and its extraction between lo and hi must contain at least one bit, 
    assert(lo ==0); // ...this forces these two assertions
    select_term_t* desc = bit_term_desc(terms, t);
    term_t tvar           = desc->arg; // Get variable (as a term)
    uint32_t selected_bit = desc->idx; // Get the bit that is selected in that variable
    return bv_slicing_sstack(ctx, tvar, selected_bit+1, selected_bit, tail, todo, slices);
  }
  case BV_EQ_ATOM: // TODO?
  case CONSTANT_TERM: // TODO?
  case BV_CONSTANT: // TODO?
  case BV64_CONSTANT: // TODO?
  default: // We consider the term is a variable, we immediately stack its relevant slices
    return bv_slicing_sstack(ctx, t, hi, lo, tail, todo, slices);
  }

}

// Prints a slicing.
void bv_slicing_print_slicing(slicing_t* slicing, term_table_t* terms, FILE* out){

  fprintf(out, "Slices:\n");
  // We go through all variables, and destroy all slices
  ptr_hmap_pair_t* hp = ptr_hmap_first_record(&slicing->slices);
  while(hp != NULL) {
    bv_slicing_print_slice(hp->val, terms, out);
    hp = ptr_hmap_next_record(&slicing->slices, hp);
    fprintf(out, "\n");
  }
  fprintf(out, "Constraints:\n");
  for (uint32_t i = 0; i < slicing->nconstraints; i++){
    if (i == 0)
      fprintf(out, "Equal.: ");
    else
      fprintf(out, "Dis.%d: ",i);
    bv_slicing_print_splist(slicing->constraints[i], (i == 0), terms, out);
    fprintf(out, "\n");
  }
}

// Destructs a slicing. Everything goes.
void bv_slicing_slicing_destruct(slicing_t* slicing){

  // We go through all variables, and destroy all slices
  ptr_hmap_pair_t* hp = ptr_hmap_first_record(&slicing->slices);
  while(hp != NULL) {
    bv_slicing_slice_delete(hp->val);
    hp = ptr_hmap_next_record(&slicing->slices, hp);
  }

  delete_ptr_hmap(&slicing->slices);

  for (uint32_t i = 0; i <= slicing->nconstraints; i++)
    bv_slicing_spdelete(slicing->constraints[i], true);

  safe_free(slicing->constraints);
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
    The resulting slicing is in slicing_out, which only needs to be allocated, as this function will take care of initialisation.
 */
void bv_slicing_construct(plugin_context_t* ctx, const ivector_t* conflict_core, slicing_t* slicing_out){

  init_ptr_hmap(&slicing_out->slices, 0); // We initialise the hashmap in the result

  // standard abbreviations
  term_table_t*  terms  = ctx->terms;
  const mcsat_trail_t* trail  = ctx->trail;

  // We create a "to do" queue of matching slice pairs to align
  ptr_queue_t* todo = safe_malloc(sizeof(ptr_queue_t));
  init_ptr_queue(todo, 0);
 
  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;
  term_kind_t atom_i_kind;
    
  // Counter that records the next available identifier to assign to a disequality in the core.
  // That disequality turns into a disjunction when slicing 
  uint32_t next_disjunction = 1;

  FILE* out = ctx_trace_out(ctx);
  for (uint32_t i = 0; i < conflict_core->size; i++) {
    atom_i_var   = conflict_core->data[i];
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);
    assert(is_pos_term(atom_i_term));
    atom_i_kind  = term_kind(terms, atom_i_term);
    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
      fprintf(out, "Slicing core constraint ");
      ctx_trace_term(ctx, atom_i_term);
    }

    switch (atom_i_kind) {
    case EQ_TERM :    // equality
    case BV_EQ_ATOM: { // We can only deal with equalities in this BV subtheory
      composite_term_t* atom_i_comp = (atom_i_kind == EQ_TERM)?eq_term_desc(terms, atom_i_term): bveq_atom_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      assert(is_pos_term(t0));
      assert(is_pos_term(t1));
      uint32_t constraint = 0;
      if (!atom_i_value) {
        constraint = next_disjunction;
        next_disjunction++;
      }
      uint32_t width = bv_term_bitsize(terms, t0);
      slist_t* l0 = bv_slicing_norm(ctx, t0, width, 0, NULL, todo, &slicing_out->slices);
      slist_t* l1 = bv_slicing_norm(ctx, t1, width, 0, NULL, todo, &slicing_out->slices);
      bv_slicing_align(l0, l1, constraint, todo, terms, out);      
      break;
    }
    case BIT_TERM: { // That's also in the fragment...
      slist_t* l0 = bv_slicing_norm(ctx, atom_i_term, 1, 0, NULL, todo, &slicing_out->slices);
      slist_t* l1 = bv_slicing_norm(ctx, bool2term(atom_i_value), 1, 0, NULL, todo, &slicing_out->slices);
      bv_slicing_align(l0, l1, 0, todo, terms, out);      
      break;
    }
    default:
      assert(false);
    }
  }

  // Now we know how many constraints we have, so we can allocate them in the result
  slicing_out->nconstraints = next_disjunction;
  slicing_out->constraints = safe_malloc(sizeof(splist_t*) * next_disjunction);
  for (uint32_t i = 0; i <= slicing_out->nconstraints; i++)
    slicing_out->constraints[i] = NULL;

  /* fprintf(out, "Finished treating core constraints, giving slicing:\n"); */
  /* bv_slicing_print_slicing(slicing_out, terms, out); */
  /* fprintf(out, "+ a \"to do\" queue.\n"); */
    
  /** While loop treating the queue of slicings to perform until the coarsest slicing has been produced */

  slist_t* l1;
  slist_t* l2;
  
  while (!ptr_queue_is_empty(todo)){
    spair_t* p = (spair_t*) ptr_queue_pop(todo);
    assert(p->lhs != NULL);
    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
      fprintf(out, "Popping ");
      bv_slicing_print_spair(p, true, terms, out);
      fprintf(out, "\n");
    }
    l1 = bv_slicing_as_list(p->lhs, NULL);
    l2 = bv_slicing_as_list(p->rhs, NULL);
    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing"))
      fprintf(out, "Now aligning\n");
    bv_slicing_align(l1, l2, p->appearing_in, todo, terms, out); // l1 and l2 are freed
    safe_free(p);
  }

  // We destruct the todo queue
  assert(ptr_queue_is_empty(todo));
  delete_ptr_queue(todo);

  // Now we go through all variables, all of their leaf slices, and collect the
  // equalities / disequalities they are involved in into slicing_out->constraints

  ptr_hmap_pair_t* hp = ptr_hmap_first_record(&slicing_out->slices);
  while(hp != NULL) {
    bv_slicing_constraints(hp->val, slicing_out->constraints);
    hp = ptr_hmap_next_record(&slicing_out->slices, hp);
  }
  
}
