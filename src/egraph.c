/*
 * EGRAPH CONSTRUCTION AND MAIN OPERATIONS
 */

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bit_tricks.h"
#include "memalloc.h"
#include "theory_explanations.h"
#include "prng.h"
#include "ptr_partitions.h"
#include "hash_functions.h"
#include "index_vectors.h"

#include "composites.h"
#include "egraph_utils.h"
#include "egraph_explanations.h"
#include "egraph.h"


#define TRACE 0

#if TRACE || 1

#include <stdio.h>
#include <inttypes.h>

#include "smt_core_printer.h"
#include "egraph_printer.h"

#endif


/*
 * Select variant implementations
 */
#define CONSERVATIVE_DISEQ_AXIOMS 0


/*****************
 *  CLASS TABLE  *
 ****************/

/*
 * Initialization: n == initial size
 */
static void init_class_table(class_table_t *tbl, uint32_t n) {
  uint32_t i;
  assert(n <  MAX_CLASS_TABLE_SIZE);

  tbl->size = n;
  tbl->nclasses = 0;

  tbl->root = (occ_t *) safe_malloc(n * sizeof(occ_t));
  tbl->dmask = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  tbl->parents = (use_vector_t *) safe_malloc(n * sizeof(use_vector_t));
  tbl->etype = (unsigned char *) safe_malloc(n * sizeof(unsigned char));
  tbl->thvar = (thvar_t *) safe_malloc(n * sizeof(thvar_t));

  // initialize all parent vectors (all empty)
  for (i=0; i<n; i++) {
    init_use_vector(tbl->parents + i, 0);
  }
}


/*
 * Increase size by 50%
 */
static void extend_class_table(class_table_t *tbl) {
  uint32_t i, n;

  n = tbl->size + 1;
  n += n>>1;

  if (n >= MAX_CLASS_TABLE_SIZE) {
    out_of_memory();
  }

  tbl->root = (occ_t *) safe_realloc(tbl->root, n * sizeof(occ_t));
  tbl->dmask = (uint32_t *) safe_realloc(tbl->dmask, n * sizeof(eterm_t));
  tbl->parents = (use_vector_t *) safe_realloc(tbl->parents, n * sizeof(use_vector_t));
  tbl->etype = (unsigned char *) safe_realloc(tbl->etype, n * sizeof(unsigned char));
  tbl->thvar = (thvar_t *) safe_realloc(tbl->thvar, n * sizeof(thvar_t));

  // initialize the new parent vectors (all empty)
  for (i=tbl->size; i<n; i++) {
    init_use_vector(tbl->parents + i, 0);
  }

  tbl->size = n;
}


/*
 * Allocate a new class
 * - nothing is initialized, except the parent vector
 * - the parent vector is empty
 */
static class_t alloc_class(class_table_t *tbl) {
  class_t i;

  i = tbl->nclasses;
  if (i >= tbl->size) {
    extend_class_table(tbl);
  }

  tbl->nclasses ++;
  assert(tbl->parents[i].nelems == 0);
  return i;
}



/*
 * Initialize a singleton class c with unique element pos_occ(t)
 * - dmask must be 0x1 if t is a constant, 0 otherwise
 * - tau = type of t
 * - x = theory variable of t
 */
static inline void init_class(class_table_t *tbl, class_t c, eterm_t t, uint32_t dmask, etype_t tau, thvar_t x) {
  tbl->root[c] = pos_occ(t);
  tbl->dmask[c] = dmask;
  tbl->etype[c] = tau;
  tbl->thvar[c] = x;
}


/*
 * Cleanup class c: free its parent vector if it's large
 * - its use vector must be empty and it must contain a single term
 */
static void free_parents(class_table_t *tbl, class_t c) {
  assert(0 < c && c < tbl->nclasses && tbl->parents[c].nelems == 0);

  // to save memory: free parent vector if it's large
  if (tbl->parents[c].size >= PARENT_DELETION_SIZE) {
    delete_use_vector(tbl->parents + c);
    init_use_vector(tbl->parents + c, 0);
  } else {
    reset_use_vector(tbl->parents + c);
  }
}




/*
 * Deletion
 */
static void delete_class_table(class_table_t *tbl) {
  uint32_t i;

  for (i=0; i<tbl->size; i++) {
    delete_use_vector(tbl->parents + i);
  }
  safe_free(tbl->parents);
  safe_free(tbl->root);
  safe_free(tbl->dmask);
  safe_free(tbl->etype);
  safe_free(tbl->thvar);

  tbl->root = NULL;
  tbl->dmask = NULL;
  tbl->parents = NULL;
  tbl->etype = NULL;
  tbl->thvar = NULL;
}


/*
 * Reset the class table
 */
static void reset_class_table(class_table_t *tbl) {
  uint32_t i;

  for (i=0; i<tbl->nclasses; i++) {
    if (tbl->parents[i].size >= PARENT_DELETION_SIZE) {
      delete_use_vector(tbl->parents + i);
      init_use_vector(tbl->parents + i, 0);
    } else {
      reset_use_vector(tbl->parents + i);
    }
  }

  tbl->nclasses = 0;
}



/****************
 *  TERM TABLE  *
 ***************/

/*
 * Initialization:
 * - n = initial size.
 */
static void init_eterm_table(eterm_table_t *tbl, uint32_t n) {
  assert(n < MAX_ETERM_TABLE_SIZE);

  tbl->size = n;
  tbl->nterms = 0;

  tbl->body = (composite_t **) safe_malloc(n * sizeof(composite_t *));
  tbl->label = (elabel_t *) safe_malloc(n * sizeof(elabel_t));
  tbl->next = (occ_t *) safe_malloc(n * sizeof(occ_t));
  tbl->edge = (int32_t *) safe_malloc(n * sizeof(int32_t));
  tbl->thvar = (thvar_t *) safe_malloc(n * sizeof(thvar_t));
  tbl->mark = allocate_bitvector(n);
  tbl->real_type = (type_t *) safe_malloc(n * sizeof(type_t));
}

/*
 * Increase size by 50%
 */
static void extend_eterm_table(eterm_table_t *tbl) {
  uint32_t n;

  n = tbl->size + 1;
  n += n >> 1;

  if (n >= MAX_ETERM_TABLE_SIZE) {
    out_of_memory();
  }

  tbl->size = n;

  tbl->body = (composite_t **) safe_realloc(tbl->body, n * sizeof(composite_t *));
  tbl->label = (elabel_t *) safe_realloc(tbl->label, n * sizeof(elabel_t));
  tbl->next = (occ_t *) safe_realloc(tbl->next, n * sizeof(occ_t));
  tbl->edge = (int32_t *) safe_realloc(tbl->edge, n * sizeof(int32_t));
  tbl->thvar = (thvar_t *) safe_realloc(tbl->thvar, n * sizeof(thvar_t));
  tbl->mark = extend_bitvector(tbl->mark, n);
  tbl->real_type = (type_t *) safe_realloc(tbl->real_type, n * sizeof(type_t));
}


/*
 * Allocate a new term with the following initialization:
 * - body = cmp
 * - egde = null_edge
 * - thvar = null_var
 * - label = null_label
 * - successor = itself
 * - real_type = NULL_TYPE
 */
static eterm_t new_eterm(eterm_table_t *tbl, composite_t *b) {
  eterm_t t;

  t = tbl->nterms;
  tbl->nterms ++;
  if (t >= tbl->size) {
    extend_eterm_table(tbl);
  }

  tbl->body[t] = b;
  tbl->label[t] = null_label;
  tbl->next[t] = pos_occ(t);
  tbl->edge[t] = null_edge;
  tbl->thvar[t] = null_thvar;
  clr_bit(tbl->mark, t);
  tbl->real_type[t] = NULL_TYPE;

  return t;
}


/*
 * Delete the full table
 */
static void delete_eterm_table(eterm_table_t *tbl) {
  uint32_t i, n;

  n = tbl->nterms;
  for (i=0; i<n; i++) {
    if (composite_body(tbl->body[i])) {
      safe_free(tbl->body[i]);
    }
  }

  safe_free(tbl->body);
  safe_free(tbl->label);
  safe_free(tbl->next);
  safe_free(tbl->edge);
  safe_free(tbl->thvar);
  delete_bitvector(tbl->mark);
  safe_free(tbl->real_type);

  tbl->body = NULL;
  tbl->label = NULL;
  tbl->next = NULL;
  tbl->edge = NULL;
  tbl->thvar = NULL;
  tbl->mark = NULL;
  tbl->real_type = NULL;
}



/*
 * Reset the term table: remove all terms
 * - atoms are deleted by emptying the egraph's atom store
 * so we don't delete them here
 */
static void reset_eterm_table(eterm_table_t *tbl) {
  uint32_t i, n;

  n = tbl->nterms;
  for (i=0; i<n; i++) {
    if (composite_body(tbl->body[i])) {
      safe_free(tbl->body[i]);
    }
  }

  tbl->nterms = 0;
}




/********************
 *  DISTINCT TABLE  *
 *******************/

static void init_distinct_table(distinct_table_t *tbl) {
  tbl->npreds = 1;
  tbl->distinct[0] = NULL;
}

static inline void reset_distinct_table(distinct_table_t *tbl) {
  init_distinct_table(tbl);
}



/***********************
 *  PROPAGATION QUEUE  *
 **********************/

/*
 * Initialize:
 * - n = initial size
 * - m = initial number of levels
 */
static void init_egraph_stack(egraph_stack_t *stack, uint32_t n, uint32_t m) {
  assert(n < MAX_EGRAPH_STACK_SIZE && 0 < m && m < MAX_EGRAPH_STACK_LEVELS);

  stack->eq = (equeue_elem_t *) safe_malloc(n * sizeof(equeue_elem_t));
  stack->etag = (unsigned char *) safe_malloc(n * sizeof(unsigned char));
  stack->edata = (expl_data_t *) safe_malloc(n * sizeof(expl_data_t));
  stack->mark = allocate_bitvector(n);
  stack->top = 0;
  stack->prop_ptr = 0;
  stack->size = n;

  stack->level_index = (uint32_t *) safe_malloc(m * sizeof(uint32_t));
  stack->level_index[0] = 0;
  stack->nlevels = m;
}


/*
 * Extend the stack: increase size by 50%
 */
static void extend_egraph_stack(egraph_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;

  if (n >= MAX_EGRAPH_STACK_SIZE) {
    out_of_memory();
  }

  stack->eq = (equeue_elem_t *) safe_realloc(stack->eq, n * sizeof(equeue_elem_t));
  stack->etag = (unsigned char *) safe_realloc(stack->etag, n * sizeof(unsigned char));
  stack->edata = (expl_data_t *) safe_realloc(stack->edata, n * sizeof(expl_data_t));
  stack->mark = extend_bitvector(stack->mark, n);
  stack->size = n;
}


/*
 * Increase the number of levels by 50%
 */
static void increase_egraph_stack_levels(egraph_stack_t *stack) {
  uint32_t n;

  n = stack->nlevels + 1;
  n += n>>1;

  if (n >= MAX_EGRAPH_STACK_LEVELS) {
    out_of_memory();
  }

  stack->level_index = (uint32_t *) safe_realloc(stack->level_index, n * sizeof(uint32_t));
  stack->nlevels = n;
}



/*
 * Push equality (t1 == t2) on top of the stack
 * - return the new edge's index
 * - explanation for the new edge must be set outside this function.
 */
static int32_t egraph_stack_push_eq(egraph_stack_t *stack, occ_t t1, occ_t t2) {
  uint32_t i;

  i = stack->top;
  if (i >= stack->size) {
    extend_egraph_stack(stack);
  }
  clr_bit(stack->mark, i);
  stack->top = i+1;
  stack->eq[i].lhs = t1;
  stack->eq[i].rhs = t2;

  return i;
}



/*
 * Delete the stack
 */
static void delete_egraph_stack(egraph_stack_t *stack) {
  safe_free(stack->eq);
  safe_free(stack->etag);
  safe_free(stack->edata);
  safe_free(stack->level_index); 
  delete_bitvector(stack->mark);

  stack->eq = NULL;
  stack->etag = NULL;
  stack->edata = NULL;
  stack->level_index = NULL;
  stack->mark = NULL;
}



/*
 * Empty the stack
 */
static void reset_egraph_stack(egraph_stack_t *stack) {
  stack->top = 0;
  stack->prop_ptr = 0;
  stack->level_index[0] = 0;
}




/****************
 *  UNDO STACK  *
 ***************/

/*
 * Initialize: n = size, m = number of levels
 */
static void init_undo_stack(undo_stack_t *stack, uint32_t n, uint32_t m) {
  assert(n < MAX_EGRAPH_STACK_SIZE && 0 < m && m < MAX_EGRAPH_STACK_LEVELS);

  stack->tag = (unsigned char *) safe_malloc(n * sizeof(unsigned char));
  stack->data = (undo_t *) safe_malloc(n * sizeof(undo_t));
  stack->top = 0;
  stack->size = n;

  stack->level_index = (uint32_t  *) safe_malloc(m * sizeof(uint32_t));
  stack->level_index[0] = 0;
  stack->nlevels = m;
}

/*
 * Extend by 50%
 */
static void extend_undo_stack(undo_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;

  if (n >= MAX_EGRAPH_STACK_SIZE) {
    out_of_memory();
  }

  stack->tag = (unsigned char *) safe_realloc(stack->tag, n * sizeof(unsigned char));
  stack->data = (undo_t *) safe_realloc(stack->data, n * sizeof(undo_t));
  stack->size = n;
}

/*
 * Increase the number of levels
 */
static void increase_undo_stack_levels(undo_stack_t *stack) {
  uint32_t n;

  n = stack->nlevels + 1;
  n += n >> 1;

  if (n >= MAX_EGRAPH_STACK_LEVELS) {
    out_of_memory();
  }

  stack->level_index = (uint32_t *) safe_realloc(stack->level_index, n * sizeof(uint32_t));
  stack->nlevels = n;
}



/*
 * Push undo objects
 */
static inline uint32_t undo_stack_get_top(undo_stack_t *stack) {
  uint32_t i;

  i = stack->top;
  if (i >= stack->size) {
    extend_undo_stack(stack);
  }
  stack->top = i+1;

  return i;
}


/*
 * Save t and its class label l, just before the class of t is merged 
 * with another class. This happens when an equality (t == u) is processed,
 */
static void undo_stack_push_merge(undo_stack_t *stack, occ_t t, elabel_t l) {
  uint32_t i;

  i = undo_stack_get_top(stack);
  stack->tag[i] = UNDO_MERGE;
  stack->data[i].merge.saved_occ = t;
  stack->data[i].merge.saved_label = l;
}


/*
 * Assertion (distinct t_0 ... t_n-1) == true
 * - the atom can be recovered from the distinct_table so
 * we just need to put a mark that DISTINCT was asserted
 */
static void undo_stack_push_distinct(undo_stack_t *stack) {
  uint32_t i;

  i = undo_stack_get_top(stack);
  stack->tag[i] = UNDO_DISTINCT;
}

// push pointer + tag
static void undo_stack_push_ptr(undo_stack_t *stack, void *p, undo_tag_t tag) {
  uint32_t i;

  i = undo_stack_get_top(stack);
  stack->tag[i] = tag;
  stack->data[i].ptr = p;  
}

/*
 * UNDO_SIMPLIFY means that cmp was simplified and removed from the congruence
 * table and use vectors (outside of a merge-class operation). On backtracking, 
 * we need to put cmp back into both tables.
 */
static inline void undo_stack_push_composite(undo_stack_t *stack, composite_t *cmp) {
  undo_stack_push_ptr(stack, cmp, UNDO_SIMPLIFY);
}

/*
 * REANALYZE_CONGRUENCE_ROOT and REANALYZE_COMPOSITE means that cmp was created on the fly,
 * and that its signature and class must be recomputed when we backtrack.
 * - REANALYZE_CONGRUENCE_ROOT means that cmp was activated as a congruence root
 * - REANALYZE_COMPOSITE measn that cmp was equal to another term when activated
 */
static inline void undo_stack_push_congruence_root(undo_stack_t *stack, composite_t *cmp) {
  undo_stack_push_ptr(stack, cmp, REANALYZE_CONGRUENCE_ROOT);
}

static inline void undo_stack_push_simplified_composite(undo_stack_t *stack, composite_t *cmp) {
  undo_stack_push_ptr(stack, cmp, REANALYZE_COMPOSITE);
}



/*
 * Delete
 */
static void delete_undo_stack(undo_stack_t *stack) {
  safe_free(stack->tag);
  safe_free(stack->data);
  safe_free(stack->level_index);

  stack->tag = NULL;
  stack->data = NULL;
  stack->level_index = NULL;
}


/*
 * Empty the stack
 */
static void reset_undo_stack(undo_stack_t *stack) {
  stack->top = 0;
  stack->level_index[0] = 0;
}


/*****************
 *  TRAIL STACK  *
 ****************/

/*
 * Initialize a trail stack: size = 0
 */
static void init_egraph_trail(egraph_trail_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}


/*
 * Save level:
 * - nt = number of terms
 * - p = progation pointer
 */
static void egraph_trail_save(egraph_trail_stack_t *stack, uint32_t nt, uint32_t p) {
  uint32_t i, n;

  i = stack->top;
  n = stack->size;
  if (i == n) {
    if (n == 0) {
      n = DEFAULT_EGRAPH_TRAIL_SIZE;
    } else {
      n += n;
      if (n >= MAX_EGRAPH_TRAIL_SIZE) {
	out_of_memory();
      }
    }
    stack->data = (egraph_trail_t *) safe_realloc(stack->data, n * sizeof(egraph_trail_t));
    stack->size = n;
  }
  stack->data[i].nterms = nt;
  stack->data[i].prop_ptr = p;

  stack->top = i + 1;
}


/*
 * Get top record
 */
static inline egraph_trail_t *egraph_trail_top(egraph_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Remove top record
 */
static inline void egraph_trail_pop(egraph_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Empty the stack
 */
static inline void reset_egraph_trail(egraph_trail_stack_t *stack) {
  stack->top = 0;
}

/*
 * Delete
 */
static inline void delete_egraph_trail(egraph_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}



/***********************
 *  STATISTICS RECORD  *
 **********************/

/*
 * Initialze all counters to 0
 */
static void init_egraph_stats(egraph_stats_t *s) {
  s->app_reductions = 0;

  s->eq_props = 0;
  s->th_props = 0;
  s->th_conflicts = 0;
  s->nd_lemmas = 0;

  s->aux_eqs = 0;
  s->boolack_lemmas = 0;
  s->ack_lemmas = 0;

  s->final_checks = 0;
  s->interface_eqs = 0;
}

/*
 * Reset: same thing
 */
static inline void reset_egraph_stats(egraph_stats_t *s) {
  init_egraph_stats(s);
}






/*************
 *   MODEL   *
 ************/

/*
 * Initialize mdl: no memory is allocated yet.
 */
static void init_egraph_model(egraph_model_t *mdl) {
  mdl->value = NULL;
  mdl->pstore = NULL;
  mdl->nat_ctr = 0;
  mdl->bv_ctr = 0;
  q_init(&mdl->arith_buffer);
  init_bvconstant(&mdl->bv_buffer);
}


/*
 * Delete mdl: free all the memory it uses
 */
static void delete_egraph_model(egraph_model_t *mdl) {
  safe_free(mdl->value);  
  mdl->value = NULL;
  if (mdl->pstore != NULL) {
    delete_pstore(mdl->pstore);
    safe_free(mdl->pstore);
    mdl->pstore = NULL;
  }
  q_clear(&mdl->arith_buffer);
  delete_bvconstant(&mdl->bv_buffer);
}


/*
 * Reset mdl: delete everything except the bv buffer
 */
static void reset_egraph_model(egraph_model_t *mdl) {
  safe_free(mdl->value);
  mdl->value = NULL;
  if (mdl->pstore != NULL) {
    delete_pstore(mdl->pstore);
    safe_free(mdl->pstore);
    mdl->pstore = NULL;
  }
  q_clear(&mdl->arith_buffer);
}




/***********************
 *  ATOM CONSTRUCTION  *
 **********************/

/*
 * Create atom <v, t> and add it to the core
 * - v must be a boolean variable in egraph->core, with no atom attached 
 * - t must be a boolean term in egraph
 */
static void create_egraph_atom(egraph_t *egraph, bvar_t v, eterm_t t) {
  atom_t *atom;
  smt_core_t *core;

  core = egraph->core;

  assert(core != NULL && bvar_atom(core, v) == NULL);

  atom = (atom_t *) objstore_alloc(&egraph->atom_store);
  atom->eterm = t;
  atom->boolvar = v;
  atom->next = atom;

  attach_atom_to_bvar(core, v, tagged_egraph_atom(atom));
}


/*
 * Swap the successors of atom1 and atom2
 * - if they are in different circular list, this merge the two lists
 * - if they are in the same list, this splits it into two
 */
static inline void swap_next_atoms(atom_t *atom1, atom_t *atom2) {
  atom_t *aux;

  aux = atom1->next; 
  atom1->next = atom2->next;
  atom2->next = aux;
}


/*
 * For debugging only: check whether two atom lists are equal or disjoint
 */
#ifndef NDEBUG

/*
 * Scan list starting from atom1, until either atom1 or atom2 is found
 */
static atom_t *scan_atom_list(atom_t *atom1, atom_t *atom2) {
  atom_t *a;
  a = atom1;
  do {
    a = a->next;
  } while (a != atom1 && a != atom2);

  return a;
}

static bool disjoint_atom_lists(atom_t *atom1, atom_t *atom2) {
  return scan_atom_list(atom1, atom2) == atom1;
}

static bool equal_atom_lists(atom_t *atom1, atom_t *atom2) {
  return scan_atom_list(atom1, atom2) == atom2;
}

#endif


/*
 * Aliases for swap_next_atoms
 */
static inline void merge_atom_lists(atom_t *atom1, atom_t *atom2) {
  assert(disjoint_atom_lists(atom1, atom2));
  swap_next_atoms(atom1, atom2);
}

static inline void split_atom_lists(atom_t *atom1, atom_t *atom2) {
  assert(equal_atom_lists(atom1, atom2));
  swap_next_atoms(atom1, atom2);
}


/*
 * Delete atom and remove it from the core.
 */
static void delete_egraph_atom(egraph_t *egraph, atom_t *atom) {
  smt_core_t *core;
  bvar_t v;

  core = egraph->core;
  v = atom->boolvar;

  assert(core != NULL && bvar_atom(core, v) == tagged_egraph_atom(atom));
  assert(atom->next == atom);

  remove_bvar_atom(core, v);
  objstore_free(&egraph->atom_store, atom);
}


/*
 * Get the egraph atom attached to a boolean variable v
 * return NULL if v has no atom or if the atom of v is not in an egraph atom
 */
static atom_t *get_egraph_atom_for_bvar(egraph_t *egraph, bvar_t v) {
  smt_core_t *core;
  void *a;

  core = egraph->core;
  assert(core != NULL);

  a = bvar_atom(core, v);
  if (a != NULL && atom_tag(a) == EGRAPH_ATM_TAG) {
    return (atom_t *)a;
  }
  return NULL;  
}






/************************
 *  TERM CONSTRUCTION   *
 ***********************/

/*
 * Create a composite term
 */
static eterm_t new_composite_eterm(egraph_t *egraph, composite_t *cmp) {
  eterm_t t;
  t = new_eterm(&egraph->terms, cmp);
  cmp->id = t;
  return t;
}

static eterm_t new_apply(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a) {
  return new_composite_eterm(egraph, new_apply_composite(f, n, a));
}

static eterm_t new_update(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, occ_t v) {
  return new_composite_eterm(egraph, new_update_composite(f, n, a, v));
}

static eterm_t new_tuple(egraph_t *egraph, uint32_t n, occ_t *a) {
  return new_composite_eterm(egraph, new_tuple_composite(n, a));
}

static eterm_t new_ite(egraph_t *egraph, occ_t t1, occ_t t2, occ_t t3) {
  return new_composite_eterm(egraph, new_ite_composite(t1, t2, t3));
}

static eterm_t new_eq(egraph_t *egraph, occ_t t1, occ_t t2) {
  return new_composite_eterm(egraph, new_eq_composite(t1, t2));
}

static eterm_t new_or(egraph_t *egraph, uint32_t n, occ_t *a) {
  return new_composite_eterm(egraph, new_or_composite(n, a));
}

// fails if too many distinct terms already exist (return null_eterm)
static eterm_t new_distinct(egraph_t *egraph, uint32_t n, occ_t *a) {
  if (egraph->ndistincts >= MAX_DISTINCT_TERMS) {
    return null_eterm;
  }
  egraph->ndistincts ++;

  return new_composite_eterm(egraph, new_distinct_composite(n, a));
}




/*
 * HASH CONSING FOR COMPOSITES
 */

/*
 * Hash-consing interface objects
 */
typedef struct {
  int_hobj_t m;
  egraph_t *egraph;
  occ_t f;
  uint32_t n;
  occ_t *a;
} apply_hobj_t;

typedef struct {
  int_hobj_t m;
  egraph_t *egraph;
  occ_t f;
  uint32_t n;
  occ_t *a;
  occ_t v;
} update_hobj_t;

// hobj type used for tuple, distinct, and or
typedef struct {
  int_hobj_t m;
  egraph_t *egraph;
  uint32_t n;
  occ_t *a;
} composite_hobj_t; 

typedef struct {
  int_hobj_t m;
  egraph_t *egraph;
  occ_t t1, t2;
} eq_hobj_t;

typedef struct {
  int_hobj_t m;
  egraph_t *egraph;
  occ_t t1, t2, t3;
} ite_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_apply_obj(apply_hobj_t *p) {
  return hash_apply(p->f, p->n, p->a);
}

static uint32_t hash_update_obj(update_hobj_t *p) {
  return hash_update(p->f, p->n, p->a, p->v);
}

static uint32_t hash_tuple_obj(composite_hobj_t *p) {
  return hash_tuple(p->n, p->a);
}

static uint32_t hash_eq_obj(eq_hobj_t *p) {
  return hash_eq(p->t1, p->t2);
}

static uint32_t hash_ite_obj(ite_hobj_t *p) {
  return hash_ite(p->t1, p->t2, p->t3);
}

static uint32_t hash_distinct_obj(composite_hobj_t *p) {
  return hash_distinct(p->n, p->a);
}

static uint32_t hash_or_obj(composite_hobj_t *p) {
  return hash_or(p->n, p->a);
}


/*
 * Equality tests
 */
static bool equal_apply_obj(apply_hobj_t *p, eterm_t i) {
  composite_t *c;

  c = p->egraph->terms.body[i];
  assert(composite_body(c));
  
  return equal_apply(c, p->f, p->n, p->a);
}

static bool equal_update_obj(update_hobj_t *p, eterm_t i) {
  composite_t *c;

  c = p->egraph->terms.body[i];
  assert(composite_body(c));

  return equal_update(c, p->f, p->n, p->a, p->v);
}

static bool equal_tuple_obj(composite_hobj_t *p, eterm_t i) {
  composite_t *c;

  c = p->egraph->terms.body[i];
  assert(composite_body(c));

  return equal_tuple(c, p->n, p->a);
}

static bool equal_eq_obj(eq_hobj_t *p, eterm_t i) {
  composite_t *c;

  c = p->egraph->terms.body[i];
  assert(composite_body(c));

  return equal_eq(c, p->t1, p->t2);
}

static bool equal_ite_obj(ite_hobj_t *p, eterm_t i) {
  composite_t *c;

  c = p->egraph->terms.body[i];
  assert(composite_body(c));

  return equal_ite(c, p->t1, p->t2, p->t3);
}

static bool equal_distinct_obj(composite_hobj_t *p, eterm_t i) {
  composite_t *c;

  c = p->egraph->terms.body[i];
  assert(composite_body(c));

  return equal_distinct(c, p->n, p->a);
}

static bool equal_or_obj(composite_hobj_t *p, eterm_t i) {
  composite_t *c;

  c = p->egraph->terms.body[i];
  assert(composite_body(c));

  return equal_or(c, p->n, p->a);
}


/*
 * Build functions
 */
static eterm_t build_apply_obj(apply_hobj_t *p) {
  return new_apply(p->egraph, p->f, p->n, p->a);
}

static eterm_t build_update_obj(update_hobj_t *p) {
  return new_update(p->egraph, p->f, p->n, p->a, p->v);
}

static eterm_t build_tuple_obj(composite_hobj_t *p) {
  return new_tuple(p->egraph, p->n, p->a);
}

static eterm_t build_eq_obj(eq_hobj_t *p) {
  return new_eq(p->egraph, p->t1, p->t2);
}

static eterm_t build_ite_obj(ite_hobj_t *p) {
  return new_ite(p->egraph, p->t1, p->t2, p->t3);
}

static eterm_t build_distinct_obj(composite_hobj_t *p) {
  return new_distinct(p->egraph, p->n, p->a);
}

static eterm_t build_or_obj(composite_hobj_t *p) {
  return new_or(p->egraph, p->n, p->a);
}


/*
 * Interface objects:
 * type coercion are necessary to stop GCC warnings
 */
static apply_hobj_t apply_hobj = {
  { (hobj_hash_t) hash_apply_obj, (hobj_eq_t) equal_apply_obj, (hobj_build_t) build_apply_obj },  
  NULL,
  0, 0, NULL,
};

static update_hobj_t update_hobj = {
  { (hobj_hash_t) hash_update_obj, (hobj_eq_t) equal_update_obj, (hobj_build_t) build_update_obj },
  NULL,
  0, 0, NULL, 0,
};

static composite_hobj_t tuple_hobj = {
  { (hobj_hash_t) hash_tuple_obj, (hobj_eq_t) equal_tuple_obj, (hobj_build_t) build_tuple_obj },
  NULL,
  0, NULL,
};

static eq_hobj_t eq_hobj = {
  { (hobj_hash_t) hash_eq_obj, (hobj_eq_t) equal_eq_obj, (hobj_build_t) build_eq_obj },
  NULL,
  0, 0,
};


static ite_hobj_t ite_hobj = {
  { (hobj_hash_t) hash_ite_obj, (hobj_eq_t) equal_ite_obj, (hobj_build_t) build_ite_obj },
  NULL,
  0, 0, 0,
};

static composite_hobj_t distinct_hobj = {
  { (hobj_hash_t) hash_distinct_obj, (hobj_eq_t) equal_distinct_obj, (hobj_build_t) build_distinct_obj },
  NULL,
  0, NULL,
};

static composite_hobj_t or_hobj = {
  { (hobj_hash_t) hash_or_obj, (hobj_eq_t) equal_or_obj, (hobj_build_t) build_or_obj },
  NULL,
  0, NULL,
};



/*
 * Hash-consing constructors
 */
static eterm_t egraph_apply_term(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a) {
  apply_hobj.egraph = egraph;
  apply_hobj.f = f;
  apply_hobj.n = n;
  apply_hobj.a = a;

  return int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &apply_hobj);
}

static eterm_t egraph_update_term(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, occ_t v) {
  update_hobj.egraph = egraph;
  update_hobj.f = f;
  update_hobj.n = n;
  update_hobj.a = a;
  update_hobj.v = v;

  return int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &update_hobj);
}

static eterm_t egraph_tuple_term(egraph_t *egraph, uint32_t n, occ_t *a) {
  tuple_hobj.egraph = egraph;
  tuple_hobj.n = n;
  tuple_hobj.a = a;

  return int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &tuple_hobj);
}

static eterm_t egraph_eq_term(egraph_t *egraph, occ_t t1, occ_t t2) {
  eq_hobj.egraph = egraph;
  eq_hobj.t1 = t1;
  eq_hobj.t2 = t2;

  return int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &eq_hobj);
}

static eterm_t egraph_ite_term(egraph_t *egraph, occ_t t1, occ_t t2, occ_t t3) {
  ite_hobj.egraph = egraph;
  ite_hobj.t1 = t1;
  ite_hobj.t2 = t2;
  ite_hobj.t3 = t3;

  return int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &ite_hobj);
}

static eterm_t egraph_distinct_term(egraph_t *egraph, uint32_t n, occ_t *a) {
  assert(n >= 3);
  
  distinct_hobj.egraph = egraph;
  distinct_hobj.n = n;
  distinct_hobj.a = a;

  return int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &distinct_hobj);
}

static eterm_t egraph_or_term(egraph_t *egraph, uint32_t n, occ_t *a) {
  or_hobj.egraph = egraph;
  or_hobj.n = n;
  or_hobj.a = a;

  return int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &or_hobj);  
}




/*
 * Search whether a composite term already exists
 * - all functions return -1 (= null_eterm) if the term requested isn't present
 * - they return the eterm index otherwise
 */
static eterm_t egraph_find_apply_term(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a) {
  apply_hobj.egraph = egraph;
  apply_hobj.f = f;
  apply_hobj.n = n;
  apply_hobj.a = a;

  return int_htbl_find_obj(&egraph->htbl, (int_hobj_t *) &apply_hobj);
}

static eterm_t egraph_find_update_term(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, occ_t v) {
  update_hobj.egraph = egraph;
  update_hobj.f = f;
  update_hobj.n = n;
  update_hobj.a = a;
  update_hobj.v = v;

  return int_htbl_find_obj(&egraph->htbl, (int_hobj_t *) &update_hobj);
}

static eterm_t egraph_find_tuple_term(egraph_t *egraph, uint32_t n, occ_t *a) {
  tuple_hobj.egraph = egraph;
  tuple_hobj.n = n;
  tuple_hobj.a = a;

  return int_htbl_find_obj(&egraph->htbl, (int_hobj_t *) &tuple_hobj);
}

static eterm_t egraph_find_eq_term(egraph_t *egraph, occ_t t1, occ_t t2) {
  eq_hobj.egraph = egraph;
  eq_hobj.t1 = t1;
  eq_hobj.t2 = t2;

  return int_htbl_find_obj(&egraph->htbl, (int_hobj_t *) &eq_hobj);
}

static eterm_t egraph_find_ite_term(egraph_t *egraph, occ_t t1, occ_t t2, occ_t t3) {
  ite_hobj.egraph = egraph;
  ite_hobj.t1 = t1;
  ite_hobj.t2 = t2;
  ite_hobj.t3 = t3;

  return int_htbl_find_obj(&egraph->htbl, (int_hobj_t *) &ite_hobj);
}

static eterm_t egraph_find_distinct_term(egraph_t *egraph, uint32_t n, occ_t *a) {
  assert(n >= 3);
  
  distinct_hobj.egraph = egraph;
  distinct_hobj.n = n;
  distinct_hobj.a = a;

  return int_htbl_find_obj(&egraph->htbl, (int_hobj_t *) &distinct_hobj);
}

static eterm_t egraph_find_or_term(egraph_t *egraph, uint32_t n, occ_t *a) {
  or_hobj.egraph = egraph;
  or_hobj.n = n;
  or_hobj.a = a;

  return int_htbl_find_obj(&egraph->htbl, (int_hobj_t *) &or_hobj);  
}






/*************************************
 *  HASH CONSING FOR CONSTANT TERMS  *
 ************************************/

/*
 * Get the hash-table for constants: allocate it if needed.
 */
static int_htbl_t *egraph_get_const_htbl(egraph_t *egraph) {
  int_htbl_t *tmp;

  tmp = egraph->const_htbl;
  if (tmp == NULL) {
    tmp = (int_htbl_t *) safe_malloc(sizeof(int_htbl_t));
    init_int_htbl(tmp, 0);
    egraph->const_htbl = tmp;
  }

  return tmp;
}


/*
 * Delete the hash-table for constants if it exists
 */
static void egraph_free_const_htbl(egraph_t *egraph) {
  int_htbl_t *tmp;

  tmp = egraph->const_htbl;
  if (tmp != NULL) {
    delete_int_htbl(tmp);
    safe_free(tmp);
    egraph->const_htbl = NULL;
  }
}



/*
 * Hash consing object; a constant if defined by its type tau and its index id
 */
typedef struct {
  int_hobj_t m;
  egraph_t *egraph;
  type_t tau;
  int32_t id;
} const_hobj_t;


static inline uint32_t hash_constant(type_t tau, int32_t id) {
  return jenkins_hash_pair(tau, id, 0x1889aed2);
}

// interface to the htbl
static uint32_t hash_const_hobj(const_hobj_t *p) {
  return hash_constant(p->tau, p->id);
}

static bool equal_const_hobj(const_hobj_t *p, eterm_t i) {
  eterm_table_t *terms;

  terms = &p->egraph->terms;
  return terms->real_type[i] == p->tau && constant_body_id(terms->body[i]) == p->id;
}

// build function: just create a new term with descriptor = constant(id)
// the type must be set later, after a class is created
static eterm_t build_const_hobj(const_hobj_t *p) {
  return new_eterm(&p->egraph->terms, mk_constant_body(p->id));
}


static const_hobj_t const_hobj = {
  { (hobj_hash_t) hash_const_hobj, (hobj_eq_t) equal_const_hobj, (hobj_build_t) build_const_hobj },
  NULL,
  0, 0,
};



/*
 * Get the constant term defined by (tau, id):
 * - if that's a new term, the initialization is not complete yet
 */
static eterm_t egraph_constant_term(egraph_t *egraph, type_t tau, int32_t id) {
  int_htbl_t *const_htbl;

  const_hobj.egraph = egraph;
  const_hobj.tau = tau;
  const_hobj.id = id;

  const_htbl = egraph_get_const_htbl(egraph);

  return int_htbl_get_obj(const_htbl, (int_hobj_t *) &const_hobj);
}


/*
 * Remove the htbl record for constant term t
 */
static void egraph_delete_constant(egraph_t *egraph, eterm_t t) {
  type_t tau;
  int32_t id;
  uint32_t h;
  
  assert(egraph_term_is_constant(egraph, t) && egraph->const_htbl != NULL);

  tau = egraph_term_real_type(egraph, t);
  id = constant_body_id(egraph_term_body(egraph, t));
  h = hash_constant(tau, id);
  int_htbl_erase_record(egraph->const_htbl, h, t);
}





/**************************************************************
 *  SIMPLIFICATION OF COMPOSITES/SEARCH FOR CONGRUENCE ROOTS  *
 *************************************************************/

/*
 * All analyze_xxx functions check whether a composite p simplifies or
 * is congruent to another composite q. 
 * - if so, they add an equality to the propagation queue and return true
 * - otherwise they store p in the congruence table and use vectors, 
 *   and return false
 */

/*
 * Propagation of the form (t1 == t2) implies (p->id == x)
 */
static inline void add_eq_implies_eq(egraph_t *egraph, composite_t *p, occ_t x, occ_t t1, occ_t t2) {
  int32_t k;

  // don't add anything if (p->id == x) already holds
  if (egraph_equal_occ(egraph, pos_occ(p->id), x)) return;

  k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), x);
  egraph->stack.etag[k] = EXPL_EQ;
  egraph->stack.edata[k].t[0] = t1;
  egraph->stack.edata[k].t[1] = t2;

#if TRACE
  printf("---> EGRAPH: equality ");
  print_occurrence(stdout, pos_occ(p->id));
  printf(" == ");
  print_occurrence(stdout, x);
  printf(" implied by ");
  print_occurrence(stdout, t1);
  printf(" == ");
  print_occurrence(stdout, t2);
  printf("\n");
#endif
}


/*
 * Propagation of the form (t1 != t2) implies (p->id == x), where t1 != t2 was derived from dmasks
 * dmsk must be dmask[class(t1)] & dmask[class(t2)]
 * The implied equality is always (p->id == false), where p is an equality term.
 */
static inline void add_diseq_implies_eq(egraph_t *egraph, composite_t *p, occ_t x, 
					occ_t t1, occ_t t2, uint32_t dmsk) {
  int32_t k;
  uint32_t i;

  // don't add anything if (p->id == x) already holds
  if (egraph_equal_occ(egraph, pos_occ(p->id), x)) return;

  k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), x);

  // the tag depends on bit i of dmsk
  i = ctz(dmsk);
  assert(0 <= i && i < egraph->dtable.npreds);
  egraph->stack.etag[k] = (expl_tag_t) (i + EXPL_DISTINCT0);
  egraph->stack.edata[k].t[0] = t1;
  egraph->stack.edata[k].t[1] = t2;

#if TRACE
  printf("---> EGRAPH: equality ");
  print_occurrence(stdout, pos_occ(p->id));
  printf(" == ");
  print_occurrence(stdout, x);
  printf(" implied by dmasks\n");
#endif

}



/*
 * Basic terms: update/apply/tuple. 
 * - no simplification rule is applied
 * - compute signature and look for a congruent term
 */
static bool analyze_basic(egraph_t *egraph, composite_t *p) {
  composite_t *q;
  signature_t *sgn;
  elabel_t *label;
  int32_t k;

  label = egraph->terms.label;
  sgn = &egraph->sgn;

  signature_basic(p, label, sgn);
  q = congruence_table_get(&egraph->ctable, p, sgn, label);
  if (q != p) {
    // basic_congruence between p and q
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), pos_occ(q->id));
    egraph->stack.etag[k] = EXPL_BASIC_CONGRUENCE;
#if TRACE
    printf("---> EGRAPH: equality ");
    print_occurrence(stdout, pos_occ(p->id));
    printf(" == ");
    print_occurrence(stdout, pos_occ(q->id));
    printf(" implied by congruence\n");
    printf("---> i.e., ");
    print_composite(stdout, p);
    printf(" == ");
    print_composite(stdout, q);
    printf("\n");
#endif
    return true;
  } 

  return false;
}


/*
 * p is (eq t1 t2)
 *
 * TODO? 
 * add more simplifications for boolean equality:
 *   t1 == true  implies (eq t1 t2) == t2
 *   t1 == false implies (eq t1 t2) == (not t2)
 */
static bool analyze_eq(egraph_t *egraph, composite_t *p) {
  occ_t t1, t2;
  elabel_t l1, l2;
  uint32_t dmsk;
  composite_t *q;
  signature_t *sgn;
  elabel_t *label;
  int32_t k;

  t1 = p->child[0];
  t2 = p->child[1];
  l1 = egraph_label(egraph, t1);
  l2 = egraph_label(egraph, t2);

  // t1 == t2 implies (eq t1 t2) == true
  if (l1 == l2) {
    add_eq_implies_eq(egraph, p, true_occ, t1, t2);
    return true;
  }

  // t1 == (not t2) implies (eq t1 t2) == false
  if (l1 == opposite_label(l2)) {
    add_eq_implies_eq(egraph, p, false_occ, t1, opposite_occ(t2));
    return true;
  }

  // t1 != t2 implies (eq t1 t2) == false
  dmsk = egraph->classes.dmask[class_of(l1)] & egraph->classes.dmask[class_of(l2)];
  if (dmsk != 0) {
    // note: the test (dmask[class_of(l1)] & dmask[class_of(l2)] != 0)
    // always fails if l1 and l2 are boolean
    add_diseq_implies_eq(egraph, p, false_occ, t1, t2, dmsk);
    return true;
  }

  // check for congruence
  label = egraph->terms.label;
  sgn = &egraph->sgn;

  signature_eq(p, label, sgn);
  q = congruence_table_get(&egraph->ctable, p, sgn, label);
  if (q != p) {
    // congruence
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), pos_occ(q->id));
    /*
     * EXPL_EQ_CONGRUENCE1 is the tag in two cases:
     * 1) t == u AND v == w IMPLIES (eq t v) == (eq u w)
     * 2) t == not u AND v == not w IMPLIES (eq t v) == (eq u w)
     *    where t, u, v, w are boolean terms
     */
    if (egraph_class(egraph, q->child[0]) == class_of(l1)) {
      egraph->stack.etag[k] = EXPL_EQ_CONGRUENCE1;
    } else {
      egraph->stack.etag[k] = EXPL_EQ_CONGRUENCE2;
    }
#if TRACE
    printf("---> EGRAPH: equality ");
    print_occurrence(stdout, pos_occ(p->id));
    printf(" == ");
    print_occurrence(stdout, pos_occ(q->id));
    printf(" implied by eq congruence\n");
    printf("---> i.e., ");
    print_composite(stdout, p);
    printf(" == ");
    print_composite(stdout, q);
    printf("\n");
#endif
    return true;
  } 

  return false;  
}


/*
 * p is (ite t1 t2 t3)
 */
static bool analyze_ite(egraph_t *egraph, composite_t *p) {
  occ_t t1, t2, t3;
  elabel_t l1, l2, l3;
  composite_t *q;
  signature_t *sgn;
  elabel_t *label;
  int32_t k;

  t1 = p->child[0];
  t2 = p->child[1];
  t3 = p->child[2];

  l1 = egraph_label(egraph, t1);

  // t1 == true implies (ite t1 t2 t3) == t2
  if (l1 == true_label) {
    add_eq_implies_eq(egraph, p, t2, t1, true_occ);
    return true;
  }

  // t1 == false implies (ite t1 t2 t3) == t3
  if (l1 == false_label) {
    add_eq_implies_eq(egraph, p, t3, t1, false_occ);
    return true;
  }

  // t2 == t3 implies (ite t1 t2 t3) == t2
  l2 = egraph_label(egraph, t2);
  l3 = egraph_label(egraph, t3);
  if (l2 == l3) {
    add_eq_implies_eq(egraph, p, t2, t2, t3);
    return true;
  }

  // congruence check
  label = egraph->terms.label;
  sgn = &egraph->sgn;

  signature_ite(p, label, sgn);
  q = congruence_table_get(&egraph->ctable, p, sgn, label);
  if (q != p) {
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), pos_occ(q->id));
    if (egraph_label(egraph, q->child[0]) == l1) {
      egraph->stack.etag[k] = EXPL_ITE_CONGRUENCE1;
    } else {
      assert(egraph_label(egraph, q->child[0]) == opposite_label(l1));
      egraph->stack.etag[k] = EXPL_ITE_CONGRUENCE2;
    }
#if TRACE
    printf("---> EGRAPH: equality ");
    print_occurrence(stdout, pos_occ(p->id));
    printf(" == ");
    print_occurrence(stdout, pos_occ(q->id));
    printf(" implied by ite congruence\n");
#endif
    return true;
  }

  return false;
}

/*
 * p is (distinct t1 ... t_n)
 */
static bool analyze_distinct(egraph_t *egraph, composite_t *p) {
  composite_t *q;
  signature_t *sgn;
  elabel_t *label;
  uint32_t i, n;
  int32_t k;

  label = egraph->terms.label;
  sgn = &egraph->sgn;
  signature_distinct(p, label, sgn);
  // sgn = labels of t1 ... t_n in increasing order

  n = composite_arity(p);
  assert(tag_arity(sgn->tag) == n);
  for (i=0; i<n-1; i++) {
    // t_i == t_j implies (distinct t1 ... t_n) == false
    if (sgn->sigma[i] == sgn->sigma[i+1]) {
      k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), false_occ);
      gen_distinct_simpl_antecedent(egraph, p, sgn->sigma[i], k);
#if TRACE
      printf("---> EGRAPH: distinct term ");
      print_occurrence(stdout, pos_occ(p->id));
      printf(" reduced to false because ");
      print_occurrence(stdout, egraph->stack.edata[k].t[0]);
      printf(" == ");
      print_occurrence(stdout, egraph->stack.edata[k].t[1]);
      printf("\n");
#endif
      return true;
    }
  }

  // check for congruence
  q = congruence_table_get(&egraph->ctable, p, sgn, label);
  if (q != p) {
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), pos_occ(q->id));
    gen_distinct_congruence_antecedent(egraph, p, q, k);
#if TRACE
    printf("---> EGRAPH: equality ");
    print_occurrence(stdout, pos_occ(p->id));
    printf(" == ");
    print_occurrence(stdout, pos_occ(q->id));
    printf(" implied by distinct congruence\n");
    printf("---> i.e., ");
    print_composite(stdout, p);
    printf(" == ");
    print_composite(stdout, q);
    printf("\n");
#endif
    return true;
  }

  return false;
}


/*
 * p is (or t_1 ... t_n)
 */
static occ_t find_child_label(egraph_t *egraph, composite_t *p, elabel_t x) {
  uint32_t i, n;
  occ_t t;

  n = composite_arity(p);
  for (i=0; i<n; i++) {
    t = p->child[i];
    if (egraph_label(egraph, t) == x) return t;
  }
  return null_occurrence;
}


static bool analyze_or(egraph_t *egraph, composite_t *p) {
  composite_t *q;
  signature_t *sgn;
  elabel_t *label;
  uint32_t i, n;
  int32_t k;
  occ_t t, u;

  label = egraph->terms.label;
  sgn = &egraph->sgn;
  signature_or(p, label, sgn);

  // sgn = labels of t_1 ... t_n in increasing order
  // with duplicates and false_labels removed
  n = tag_arity(sgn->tag);

  if (n == 0) {
    // (or t_1 ... t_n) == false
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), false_occ);
    egraph->stack.etag[k] = EXPL_SIMP_OR;
#if TRACE
      printf("---> EGRAPH: or term ");
      print_occurrence(stdout, pos_occ(p->id));
      printf(" = ");
      print_composite(stdout, p);
      printf(" reduced to false\n");
#endif
    return true;
  }

  // if one t_i == true then true_label is in sgn->sigma[0]
  if (sgn->sigma[0] == true_label) {
    t = find_child_label(egraph, p, true_label);
    assert(t >= 0);
    add_eq_implies_eq(egraph, p, true_occ, t, true_occ);
    return true;
  }

  if (n == 1) {
    // (or t_1 ... t_n) == t
    t = find_child_label(egraph, p, sgn->sigma[0]);
    assert(t >= 0);
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), t);
    egraph->stack.etag[k] = EXPL_SIMP_OR;
#if TRACE
      printf("---> EGRAPH: or term ");
      print_occurrence(stdout, pos_occ(p->id));
      printf(" = ");
      print_composite(stdout, p);
      printf(" reduced to ");
      print_occurrence(stdout, t);
      printf("\n");
#endif
    return true;
  }

  // check for complementary labels
  for (i=1; i<n; i++) {
    if (sgn->sigma[i] == opposite_label(sgn->sigma[i-1])) {
      t = find_child_label(egraph, p, sgn->sigma[i]);
      u = find_child_label(egraph, p, sgn->sigma[i-1]);
      assert(t >= 0 && u >= 0);
      assert(egraph_label(egraph, u) == opposite_label(egraph_label(egraph, t)));

      // t == (not u) implies (or ... t ... u ...) == true
      add_eq_implies_eq(egraph, p, true_occ, t, opposite_occ(u));

      return true;
    }
  }

  // check for congruence
  q = congruence_table_get(&egraph->ctable, p, sgn, label);
  if (q != p) {
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(p->id), pos_occ(q->id));
    gen_or_congruence_antecedent(egraph, p, q, k);
#if TRACE
    printf("---> EGRAPH: equality ");
    print_occurrence(stdout, pos_occ(p->id));
    printf(" == ");
    print_occurrence(stdout, pos_occ(q->id));
    printf(" implied by or congruence\n");
    printf("---> i.e., ");
    print_composite(stdout, p);
    printf(" == ");
    print_composite(stdout, q);
    printf("\n");
#endif
    return true;
  }

  return false;
}



static bool composite_simplifies(egraph_t *egraph, composite_t *p) {
  // use a jump table rather than switch??
  switch (composite_kind(p)) {
  case COMPOSITE_APPLY:
  case COMPOSITE_UPDATE:
  case COMPOSITE_TUPLE:
    return analyze_basic(egraph, p);

  case COMPOSITE_EQ:
    return analyze_eq(egraph, p);

  case COMPOSITE_ITE:
    return analyze_ite(egraph, p);

  case COMPOSITE_DISTINCT:
    return analyze_distinct(egraph, p);

  case COMPOSITE_OR:
    return analyze_or(egraph, p);
  }

  assert(false);
  return false;
}




/*********************
 *  TERM ACTIVATION  *
 ********************/

/*
 * Check whether t is a newly created term (not active yet)
 */
static inline bool egraph_term_is_fresh(egraph_t *egraph, eterm_t t) {
  assert(0 <= t && t < egraph->terms.nterms);
  return egraph->terms.label[t] == null_label;
}


/*
 * Add composite d to the congruence table and use vectors
 * - if d is created at decision_level > 0 push d
 *   on the undo stack to be reanalyzed after backtracking. 
 * - check whether t is equal to another term u and if so
 *   push the equality (t == u)
 */
static void egraph_activate_composite(egraph_t *egraph, composite_t *d) {
  undo_tag_t tag;

  assert(composite_body(d) && egraph->decision_level >= egraph->base_level);

  tag = REANALYZE_COMPOSITE;

  if (! composite_simplifies(egraph, d)) {
    /*
     * d is a congruence root
     * - composite_simplifies has added d to the congruence table
     * - we need to add it to the parent vectors
     */
    attach_composite(d, egraph->terms.label, egraph->classes.parents);
    tag = REANALYZE_CONGRUENCE_ROOT;

  }

  /*
   * If decision_level > base_level, we'll have to reanalyze d 
   * after backtracking.
   *
   * If decision_level == base_level and base_level > 0, we'll also
   * have to reanalyze d on the next call to egraph_pop.  This will
   * force d to be removed from the parent vector and congruence table.
   */
  //  if (egraph->decision_level > egraph->base_level) {
  if (egraph->decision_level > 0) {
    undo_stack_push_ptr(&egraph->undo, d, tag);
  }
}

/*
 * Attach variable v and type tau then activate term t:
 * - add t to a fresh singleton class c
 *
 * HACK: don't do a full activation for (distinct ...) terms
 * - it's enough to just add them to a singleton class.
 * - maintaining them into the congruence table and parent vectors 
 *   is usually a waste of time.
 */
static void egraph_activate_term(egraph_t *egraph, eterm_t t, etype_t tau, thvar_t x) {
  class_t c;
  composite_t *d;
  uint32_t dmask;

  assert(egraph_term_is_fresh(egraph, t));

  c = alloc_class(&egraph->classes);
  d = egraph->terms.body[t];
  egraph->terms.label[t] = pos_label(c);
  egraph->terms.thvar[t] = x;

  dmask = 0x0;
  if (constant_body(d)) dmask = 0x1;
  init_class(&egraph->classes, c, t, dmask, tau, x);

  if (composite_body(d) && composite_kind(d) != COMPOSITE_DISTINCT) {
    egraph_activate_composite(egraph, d);
  }
}





/******************************************
 *  EQUALITY/DISTINCT/DISEQUALITY CHECKS  *
 *****************************************/

/*
 * Check whether t1 and t2 are known to be disequal
 * Returns true in the following cases:
 * 1) t1 and (not t2) are equal
 * 2) there are distinct constants a1 and a2 with t1 == a1 and t2 == a2
 * 3) there's a term v = (eq u1 u2), such that v == false, and 
 *     t1 == u1, t2 == u2 or t1 == u2, t2 == u1
 * 4) there's a term v = (distinct u_1 ... u_n) such that v == true,
 *    and t1 == u_i and t2 == u_j with i /= j
 * 5) t1 and t2 are attached to two theory variables x1 and x2,
 *    and the theory solver knows that x1 != x2
 */
bool egraph_check_diseq(egraph_t *egraph, occ_t t1, occ_t t2) {
  uint32_t *dmask;
  composite_t *eq;
  class_t c1, c2;

  c1 = egraph_class(egraph, t1);
  c2 = egraph_class(egraph, t2);

  if (c1 == c2) {
    return polarity_of_occ(t1) != polarity_of_occ(t2);
  }

  dmask = egraph->classes.dmask;
  if ((dmask[c1] & dmask[c2]) != 0) {
    return true;
  }
  
  eq = congruence_table_find_eq(&egraph->ctable, t1, t2, egraph->terms.label);
  return eq != NULL_COMPOSITE && egraph_occ_is_false(egraph, pos_occ(eq->id));
}



/*
 * Check whether t1 and t2 are disequal via the theory solver
 * Return true if t1 and t2 are attached to two theory variables x1 and x2
 * and the corresponding theory solver knows that x1 and x2 are distinct.
 * - this looks at the base variables for t1 and t2
 */
bool egraph_check_theory_diseq(egraph_t *egraph, occ_t t1, occ_t t2) {
  etype_t i;
  thvar_t x1, x2;

  i = egraph_type(egraph, t1);
  switch (i) {
  case ETYPE_INT:
  case ETYPE_REAL:
  case ETYPE_BV:
  case ETYPE_FUNCTION:
    x1 = egraph_term_base_thvar(egraph, term_of_occ(t1));
    x2 = egraph_term_base_thvar(egraph, term_of_occ(t2));
    return x1 != null_thvar && x2 != null_thvar && 
      egraph->eg[i] != NULL && 
      egraph->eg[i]->check_diseq(egraph->th[i], x1, x2);
    
  default:
    return false;
  }
}





/*
 * Check whether d = (distinct u_1 ... u_n) is false.
 * Returns true if u_i == u_j for i/=j
 */
bool egraph_check_distinct_false(egraph_t *egraph, composite_t *d) {
  occ_t t;
  elabel_t x;
  uint32_t i, n;
  int_hmap_t *imap;
  int_hmap_pair_t *p;
  bool result;

  assert(composite_kind(d) == COMPOSITE_DISTINCT);

  n = composite_arity(d);
  result = false;
  imap = egraph_get_imap(egraph);

  for (i=0; i<n; i++) {
    t = d->child[i];
    x = egraph_label(egraph, t);
    p = int_hmap_get(imap, x);
    if (p->val >= 0) { 
      result = true;
      break;
    }
    p->val = t;
  }

  int_hmap_reset(imap);

  return result;
}


/*
 * Check whether d = (distinct u_1 ... u_n) is true.
 * (Expensive).
 */
bool egraph_check_distinct_true(egraph_t *egraph, composite_t *d) {
  uint32_t i, j, n;
  occ_t x, y;

  assert(composite_kind(d) == COMPOSITE_DISTINCT);
  n = composite_arity(d);

  for (i=0; i<n; i++) {
    x = d->child[i];
    for (j=i+1; j<n; j++) {
      y = d->child[j];
      if (! egraph_check_diseq(egraph, x, y) && ! egraph_check_theory_diseq(egraph, x, y)) {
	return false;
      }
    }
  }

  return true;
}


/*
 * Incomplete but faster version
 */
bool egraph_fast_check_distinct_true(egraph_t *egraph, composite_t *d) {
  uint32_t *dmask;
  uint32_t i, n, dmsk;
  occ_t x;

  assert(composite_kind(d) == COMPOSITE_DISTINCT);

  n = composite_arity(d);
  assert(n > 0);

  dmask = egraph->classes.dmask;
  dmsk = ~((uint32_t) 0);
  i = 0;
  do {
    x = d->child[i];
    dmsk &= dmask[egraph_class(egraph, x)];
    i ++;
  } while (dmsk != 0 && i < n);

  // dmsk trick does not rule out u_i == u_j
  return dmsk != 0 && ! egraph_check_distinct_false(egraph, d);
}






/*******************************************
 *   PREDICATE/BOOLEAN TERM CONSTRUCTORS   *
 ******************************************/

#ifndef NDEBUG

/*
 * For debugging: check whether (t == false) is in the assertion queue
 * - i.e., t was asserted to be false, but egraph_term_is_false(egraph, t)
 *   does not hold yet.
 */
static bool egraph_term_asserted_false(egraph_t *egraph, eterm_t t) {
  equeue_elem_t *e;
  uint32_t i, n;
  occ_t u;

  u = pos_occ(t);

  n = egraph->stack.top;
  for (i=egraph->stack.prop_ptr; i<n; i++) {
    e = egraph->stack.eq + i;
    if ((e->lhs == u && e->rhs == false_occ) || 
	(e->lhs == false_occ && e->rhs == u)) {
      return true;
    }      
  }

  return false;
}

#endif


/*
 * Atoms (type = BOOL, theory variable = a fresh boolean variable)
 * - all return pos_occ(theory_variable)
 * - make_pred build an uninterpreted predicate (f a[0] ... a[n])
 * - make_distinct rewrites (distinct a[0] ... a[n-1]) to a conjunction of 
 *   disequalities if the distinct limit is reached.
 */
static literal_t egraph_term2literal(egraph_t *egraph, eterm_t t) {
  bvar_t v;

  if (egraph_term_is_fresh(egraph, t)) {
    v = create_boolean_variable(egraph->core);
    create_egraph_atom(egraph, v, t);
    egraph_set_term_real_type(egraph, t, bool_type(egraph->types));
    egraph_activate_term(egraph, t, ETYPE_BOOL, v);
  } else {
#if CONSERVATIVE_DISEQ_AXIOMS
    v = egraph->terms.thvar[t];
    assert(v != null_thvar && egraph_term_type(egraph, t) == ETYPE_BOOL);
#else
    /*
     * Hackish: this assumes that all existing boolean terms with no
     * theory variables attached are equalities asserted false (via
     * egraph_assert_diseq_axiom) at the base level.
     */
    assert(egraph_term_type(egraph, t) == ETYPE_BOOL);
    v = egraph->terms.thvar[t];
    if (v == null_thvar) {
      /*
       * This assertion is wrong: the equality t == false may no 
       * be processed yet (i.e., still in the queue). If that's the 
       * case, egraph_term_is_false(egraph, t) will return false and
       * the assertion will fail.
       */
      //      assert(egraph_term_is_eq(egraph, t) && egraph_term_is_false(egraph, t));
      assert(egraph_term_is_eq(egraph, t)); 
      assert(egraph_term_is_false(egraph, t) || egraph_term_asserted_false(egraph, t));

      return false_literal;
    }
#endif
  }

  return pos_lit(v);
}





literal_t egraph_make_pred(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a) {
  eterm_t t;
  t = egraph_apply_term(egraph, f, n, a);
  return egraph_term2literal(egraph, t);
}

literal_t egraph_make_eq(egraph_t *egraph, occ_t t1, occ_t t2) {
  occ_t aux;
  eterm_t t;

  // simplify 
  if (t1 == t2) return true_literal;

  if (egraph->base_level == egraph->decision_level) {
    if (egraph_equal_occ(egraph, t1, t2)) {
      return true_literal;
    } else if (egraph_check_diseq(egraph, t1, t2)) {
      return false_literal;
    }
  }

  if (egraph_check_theory_diseq(egraph, t1, t2)) {
    // should work at any decision level
    return false_literal;
  }

  // normalize
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  t = egraph_eq_term(egraph, t1, t2);
  return egraph_term2literal(egraph, t);
}


#if ! CONSERVATIVE_DISEQ_AXIOMS

/*
 * Variant of make_eq used by assert_diseq_axiom:
 * create a term but not the attached atom or literal
 */
static occ_t egraph_make_eq_term(egraph_t *egraph, occ_t t1, occ_t t2) {
  occ_t aux;
  eterm_t t;

  // simplify 
  if (t1 == t2) return true_occ;

  if (egraph->base_level == egraph->decision_level) {
    if (egraph_equal_occ(egraph, t1, t2)) {
      return true_occ;
    } else if (egraph_check_diseq(egraph, t1, t2) || egraph_check_theory_diseq(egraph, t1, t2)) {
      return false_occ;
    }
  }

  // normalize
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  t = egraph_eq_term(egraph, t1, t2);
  if (egraph_term_is_fresh(egraph, t)) {
    egraph_set_term_real_type(egraph, t, bool_type(egraph->types));
    egraph_activate_term(egraph, t, ETYPE_BOOL, null_thvar);
  }
  return pos_occ(t);
}

#endif

/*
 * Generate all equalities (a[i] == a[j]) for 0 <= i < j <n
 * - the result is stored as literals in vector *v
 */
static void expand_distinct(egraph_t *egraph, uint32_t n, occ_t *a, ivector_t *v) {
  uint32_t i, j;
  occ_t a_i;
  literal_t l;

  ivector_reset(v);
  for (i=0; i<n-1; i++) {
    a_i = a[i];
    for (j=i+1; j<n; j++) {
      l = egraph_make_eq(egraph, a_i, a[j]);
      ivector_push(v, l);
    }
  }
}

/*
 * Create a fresh boolean variable x and assert clauses equivalent to 
 * - not(x) == (distinct a[0] ... a[n-1])
 */
static literal_t assert_distinct_def_clauses(egraph_t *egraph, uint32_t n, occ_t *a) {
  ivector_t *v;
  literal_t l;
  uint32_t i, p;
  smt_core_t *core;

  v = &egraph->aux_buffer;
  expand_distinct(egraph, n, a, v);
  core = egraph->core;
  assert(core != NULL);
  l = pos_lit(create_boolean_variable(core));

  // clauses for pos_lit(x) == (or (eq a[0] a[1]) .... (eq a[n-1] a[n]))
  p = v->size;
  for (i=0; i<p; i++) {
    add_binary_clause(core, l, not(v->data[i]));
  }
  ivector_push(v, not(l));
  add_clause(core, p+1, v->data);

  return not(l);
}


literal_t egraph_make_distinct(egraph_t *egraph, uint32_t n, occ_t *a) {
  eterm_t t;

  /*
   * TODO: check this:
   * 1) normalize the term t? 
   * 2) always expand small distinct terms?
   */  
  t = egraph_distinct_term(egraph, n, a);
  if (t == null_eterm) {
    return assert_distinct_def_clauses(egraph, n, a);
  } else {
    return egraph_term2literal(egraph, t);
  }
}




/*
 * Boolean if-then-else
 */
literal_t egraph_make_boolean_ite(egraph_t *egraph, occ_t c, occ_t t1, occ_t t2) {
  eterm_t t;

  if (is_pos_occ(c)) {
    t = egraph_ite_term(egraph, c, t1, t2);
  } else {
    t = egraph_ite_term(egraph, opposite_occ(c), t2, t1);
  }
  return egraph_term2literal(egraph, t);
}


/*
 * OR term
 */
literal_t egraph_make_or(egraph_t *egraph, uint32_t n, occ_t *a) {
  eterm_t t;

  t = egraph_or_term(egraph, n, a);
  return egraph_term2literal(egraph, t);
}





/****************************************
 *  TEST WHETHER COMPOSITE TERMS EXIST  *
 ***************************************/

bool egraph_apply_exists(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a) {
  return egraph_find_apply_term(egraph, f, n, a) >= 0;
}

bool egraph_ite_exists(egraph_t *egraph, occ_t c, occ_t t1, occ_t t2) {
  if (is_pos_occ(c)) {
    return egraph_find_ite_term(egraph, c, t1, t2) >= 0;
  } else {
    return egraph_find_ite_term(egraph, opposite_occ(c), t2, t1) >= 0;
  }
}

bool egraph_update_exists(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, occ_t v) {
  return egraph_find_update_term(egraph, f, n, a, v) >= 0;
}

bool egraph_tuple_exists(egraph_t *egraph, uint32_t n, occ_t *a) {
  return egraph_find_tuple_term(egraph, n, a) >= 0;
}

bool egraph_eq_exists(egraph_t *egraph, occ_t t1, occ_t t2) {
  if (t1 < t2) {
    return egraph_find_eq_term(egraph, t1, t2) >= 0;
  } else {
    return egraph_find_eq_term(egraph, t2, t1) >= 0;
  }
}

bool egraph_distinct_exists(egraph_t *egraph, uint32_t n, occ_t *a) {
  return egraph_find_distinct_term(egraph, n, a) >= 0;
}

bool egraph_or_exists(egraph_t *egraph, uint32_t n, occ_t *a) {
  return egraph_find_or_term(egraph, n, a) >= 0;
}




/**********************************
 *  APPLY/UPDATE SIMPLIFICATIONS  *
 *********************************/

/*
 * Check whether (a[0], ..., a[n-1]) != (b[0],...,b[n-1]) holds at the base level
 */
static bool egraph_check_diseq_arrays(egraph_t *egraph, uint32_t n, occ_t *a, occ_t *b) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (egraph_check_diseq(egraph, a[i], b[i]) || egraph_check_theory_diseq(egraph, a[i], b[i])) {
      return true;
    }
  }
  return false;
}


/*
 * Check whether (a[0] ... a[n-1]) == (b[0] ... b[n-1]) at the current level
 */
static bool egraph_check_eq_arrays(egraph_t *egraph, uint32_t n, occ_t *a, occ_t *b) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (! egraph_check_eq(egraph, a[i], b[i])) {
      return false;
    }
  }
  return true;
}


static void auto_activate(egraph_t *egraph, eterm_t u, type_t type);

/*
 * Check whether (apply f a[0] ... a[n-1]) is reducible
 * to an existing term occurrence u.
 * - return null_occurrence if nothing is found
 */
static occ_t egraph_reduce_apply(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a) {
  composite_t *cmp;
  eterm_t t;
  occ_t g;

  g = f;
  assert(is_pos_occ(g));
  cmp = egraph_term_body(egraph, term_of_occ(g));
  while (composite_body(cmp) && composite_kind(cmp) == COMPOSITE_UPDATE) {
    assert(composite_arity(cmp) == n + 2);
    // g is (update h b[0] .. b[n-1] v)
    if (egraph_check_diseq_arrays(egraph, n, cmp->child + 1, a)) {
      // (apply g a[0] ... a[n-1]) --> (apply h a[0] ... a[n-1])
      g = composite_child(cmp, 0); // g := h
      assert(is_pos_occ(g));
      cmp = egraph_term_body(egraph, term_of_occ(g));
    } else if (egraph_check_eq_arrays(egraph, n, cmp->child + 1, a)) {
      // (apply g a[0] ... a[n-1]) --> v
      return composite_child(cmp, n+1);
    } else {
      if (g != f) {
	// (apply f a[0] ... a[n-1]) == (apply g a[0] ... a[n-1])
	// so we return (apply g a[0] ... a[n-1]).
	t = egraph_apply_term(egraph, g, n, a);
	if (egraph_term_is_fresh(egraph, t)) {
	  type_t tau;

	  tau = egraph_term_real_type(egraph, term_of_occ(g));
	  tau = function_type_range(egraph->types, tau);
	  auto_activate(egraph, t, tau);
	}
	return pos_occ(t);
      }
      break;
    }
  }

  return null_occurrence;
}



/******************************************
 *   CONSTRUCTORS FOR NON-BOOLEAN TERMS   *
 *****************************************/

/*
 * Conversion from a type tau in the type table to an egraph type
 */
static const uint8_t type_kind2etype[FUNCTION_TYPE+1] = {
  ETYPE_NONE,     // UNUSED_TYPE (should not occur)
  ETYPE_BOOL,     // BOOL_TYPE
  ETYPE_INT,      // INT_TYPE
  ETYPE_REAL,     // REAL_TYPE
  ETYPE_BV,       // BITVECTOR_TYPE
  ETYPE_NONE,     // SCALAR_TYPE
  ETYPE_NONE,     // UNINTERPRETED_TYPE
  ETYPE_NONE,     // VARIABLE_TYPE (should not occur)
  ETYPE_TUPLE,    // TUPLE_TYPE
  ETYPE_FUNCTION, // FUNCTION_TYPE
};

static inline etype_t type_to_etype(type_table_t *types, type_t tau) {
  return (etype_t) type_kind2etype[type_kind(types, tau)];
}


/*
 * Activate egraph term u and attach an adequate theory variable to u
 * - type = type for u
 */
static void auto_activate(egraph_t *egraph, eterm_t u, type_t type) {
  etype_t tau;
  thvar_t x;
  uint32_t n;

  assert(egraph_term_is_fresh(egraph, u));

  /*
   * To ensure that attach_eterm is called last:
   * 1) create a theory variable x
   * 2) activate the term u
   * 3) attach u to x in the satellite solver
   */
  tau = type_to_etype(egraph->types, type);
  x = null_thvar;
  switch (tau) {
  case ETYPE_INT:
    if (egraph->arith_smt != NULL) {
      x = egraph->arith_eg->create_arith_var(egraph->th[ETYPE_INT], true);
    }
    break;

  case ETYPE_REAL:
    if (egraph->arith_smt != NULL) {      
      x = egraph->arith_eg->create_arith_var(egraph->th[ETYPE_REAL], false);
    }
    break;

  case ETYPE_BV:
    if (egraph->bv_smt != NULL) {
      n = bv_type_size(egraph->types, type);
      x = egraph->bv_eg->create_bv_var(egraph->th[ETYPE_BV], n);
    }
    break;

  case ETYPE_FUNCTION:
    if (egraph->ctrl[ETYPE_FUNCTION] != NULL) {
      x = egraph->fun_eg->create_fun_var(egraph->th[ETYPE_FUNCTION], type);
    }
    break;

  case ETYPE_NONE:
    // no theory variable
    break;

  case ETYPE_TUPLE:
    // if u is a tuple term, theory variable = the term itself
    if (egraph_term_is_composite_tuple(egraph, u)) {
      x = u;
    }
    break;

  case ETYPE_BOOL:
    x = create_boolean_variable(egraph->core);
    create_egraph_atom(egraph, x, u);
    break;

  default:
    assert(false);
    abort();
  }

  // set the term type and activate it
  egraph_set_term_real_type(egraph, u, type);
  egraph_activate_term(egraph, u, tau, x);

  // attach u to x in the satellite solver
  if (tau <= ETYPE_FUNCTION && egraph->eg[tau] != NULL) {
    egraph->eg[tau]->attach_eterm(egraph->th[tau], x, u);
  }
  
}


/*
 * Create the constant of type tau and index id
 * - id = same index as the matching constant in the term table
 */
eterm_t egraph_make_constant(egraph_t *egraph, type_t tau, int32_t id) {
  eterm_t t;

  t = egraph_constant_term(egraph, tau, id);
  if (egraph_term_is_fresh(egraph, t)) {
    egraph_set_term_real_type(egraph, t, tau);
    egraph_activate_term(egraph, t, ETYPE_NONE, null_thvar);
  }


  return t;
}


/*
 * Create a fresh variable of type tau
 */
eterm_t egraph_make_variable(egraph_t *egraph, type_t tau) {
  eterm_t t;

  t = new_eterm(&egraph->terms, VARIABLE_BODY);
  auto_activate(egraph, t, tau);
  return t;
}


/*
 * Create a function application of type tau
 */
eterm_t egraph_make_apply(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, type_t tau) {
  eterm_t t;
  occ_t u;
  int32_t k;

  t = egraph_apply_term(egraph, f, n, a);
  if (egraph_term_is_fresh(egraph, t)) {
    auto_activate(egraph, t, tau);
    if (egraph->decision_level == egraph->base_level) {
      // check for apply/update reduction
      u = egraph_reduce_apply(egraph, f, n, a);
      if (u != null_occurrence) {
	// add (t == u) as an axiom
	k = egraph_stack_push_eq(&egraph->stack, pos_occ(t), u);
	egraph->stack.etag[k] = EXPL_AXIOM;
	egraph->stats.app_reductions ++;
      }
    }
  }
  return t;
}


/*
 * If-then-else of type tau
 */
eterm_t egraph_make_ite(egraph_t *egraph, occ_t c, occ_t t1, occ_t t2, type_t tau) {
  eterm_t t;

  if (is_pos_occ(c)) {
    t = egraph_ite_term(egraph, c, t1, t2);
  } else {
    t = egraph_ite_term(egraph, opposite_occ(c), t2, t1);
  }

  if (egraph_term_is_fresh(egraph, t)) {
    auto_activate(egraph, t, tau);
  }
  return t;
}


/*
 * Update of type tau
 */
eterm_t egraph_make_update(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, occ_t v, type_t tau) {
  eterm_t t;

  t = egraph_update_term(egraph, f, n, a, v);
  if (egraph_term_is_fresh(egraph, t)) {
    auto_activate(egraph, t, tau);
  }
  return t;
}


/*
 * Tuples: (type = tau, etype = TUPLE, theory variable = itself)
 * - the term's body is (tuple a[0], .., a[n-1])
 */
eterm_t egraph_make_tuple(egraph_t *egraph, uint32_t n, occ_t *a, type_t tau) {
  eterm_t t;

  t = egraph_tuple_term(egraph, n, a);
  if (egraph_term_is_fresh(egraph, t)) {
    auto_activate(egraph, t, tau);
  }
  return t;
}





/***************
 *  UTILITIES  *
 **************/

/*
 * Search for a tuple-term u such that u == t
 * - return null_eterm if there is none
 */
eterm_t egraph_get_tuple_in_class(egraph_t *egraph, eterm_t t) {
  eterm_t tv;
  class_t c;

  c = egraph_term_class(egraph, t);
  assert(egraph_class_is_tuple(egraph, c));
  tv = egraph_class_thvar(egraph, c);

#ifndef NDEBUG
  if (tv != null_eterm) {
    composite_t *cmp;
    cmp = egraph_term_body(egraph, tv);
    assert(composite_body(cmp) && cmp != NULL && composite_kind(cmp) == COMPOSITE_TUPLE);
  }
#endif

  return tv;
}


/*
 * Return a term t equal to boolean variable v
 * - search for an egraph atom of the form <t, v>
 * - if there is one return t
 * - otherwise, create a fresh term t (variable + BOOL type)
 *   and construct the atom <t, v>
 * - if v already has a non-egraph atom, attached,
 *   create a fresh v', assert v' == v in the core then
 *   attach t to v'
 * If a new term is created, it is activated.
 */
eterm_t egraph_bvar2term(egraph_t *egraph, bvar_t v) {
  void *atom;
  bvar_t aux;
  eterm_t t;
  smt_core_t *core;
 
  core = egraph->core;
  assert(core != NULL);

  atom = bvar_atom(core, v);
  if (atom != NULL) {
    if (atom_tag(atom) == EGRAPH_ATM_TAG) {
      return ((atom_t *) atom)->eterm;
    } else {
      aux = v;
      v = create_boolean_variable(core);
      // assert aux <=> v
      add_binary_clause(core, pos_lit(v), neg_lit(aux));
      add_binary_clause(core, neg_lit(v), pos_lit(aux));
    }
  }

  // create fresh t + new atom  <t, v>
  t = new_eterm(&egraph->terms, VARIABLE_BODY);  
  create_egraph_atom(egraph, v, t);
  egraph_set_term_real_type(egraph, t, bool_type(egraph->types));
  egraph_activate_term(egraph, t, ETYPE_BOOL, v);

  return t;
}




/*
 * Return a term t of type tau equal to theory variable v
 * - t is a fresh egraph variable
 * - v must not be attached to another term t'
 * - there must be a theory solver for the type tau
 */
eterm_t egraph_thvar2term(egraph_t *egraph, thvar_t v, type_t tau) {
  etype_t eta;
  eterm_t t;

  eta = type_to_etype(egraph->types, tau);
  assert(eta <= ETYPE_FUNCTION && egraph->eg[eta] != NULL);

  // fresh variable
  t = new_eterm(&egraph->terms, VARIABLE_BODY);

  // set the term type and activate t
  egraph_set_term_real_type(egraph, t, tau);
  egraph_activate_term(egraph, t, eta, v);

  // attach t to v in the satellite solver
  egraph->eg[eta]->attach_eterm(egraph->th[eta], v, t);

  return t;
}





/*
 * Create the built-in boolean constant
 */
static void egraph_init_constant(egraph_t *egraph) {
  eterm_t t0;

  t0 = new_eterm(&egraph->terms, mk_constant_body(0));
  assert(t0 == true_eterm);
  create_egraph_atom(egraph, const_bvar, t0);
  egraph_set_term_real_type(egraph, t0, bool_type(egraph->types));
  egraph_activate_term(egraph, t0, ETYPE_BOOL, const_bvar);
}




/**************************
 *  AUXILIARY EQUALITIES  *
 *************************/

/*
 * Auxiliary equalities are created when adding ackermann lemmas
 * To prevent blow up, we put a limit on the number of auxiliary
 * equalities created. When the limit is reached, creation of 
 * new auxiliary fails. Only lemmas that are built from existing 
 * equalities can be added at that point.
 * - the quota is stored in egraph->aux_eq_quota
 * - the number of auxiliary equalities created is in egraph->stats.aux_eqs
 */

/*
 * Variant build function for auxiliary equalities
 */
static eterm_t build_aux_eq_obj(eq_hobj_t *p) {
  egraph_t *g;

  g = p->egraph;
  if (g->stats.aux_eqs >= g->aux_eq_quota) {
    return null_eterm;
  }
  g->stats.aux_eqs ++;
  return new_eq(g, p->t1, p->t2);
}


/*
 * Hash-consing object
 */
static eq_hobj_t aux_eq_hobj = {
  { (hobj_hash_t) hash_eq_obj, (hobj_eq_t) equal_eq_obj, (hobj_build_t) build_aux_eq_obj },
  NULL,
  0, 0,
};


/*
 * Constructor for auxiliary equality:
 * - returns null_literal if the construction fails (i.e., when the quota is reached)
 */
static literal_t egraph_make_aux_eq(egraph_t *egraph, occ_t t1, occ_t t2) {
  occ_t aux;
  eterm_t t;

  if (t1 == t2) return true_literal;

  if (t1 > t2) {
    // normalize
    aux = t1; t1 = t2; t2 = aux;
  }

  // call hash-consing constructor
  aux_eq_hobj.egraph = egraph;
  aux_eq_hobj.t1 = t1;
  aux_eq_hobj.t2 = t2;
  t = int_htbl_get_obj(&egraph->htbl, (int_hobj_t *) &aux_eq_hobj);

  if (t == null_eterm) {
    return null_literal;  // quota exceeded
  } else {
    return egraph_term2literal(egraph, t);
  }
}







/************************
 *  LEMMA CONSTRUCTION  *
 ***********************/

/*
 * Distinct expansion: add the lemma
 *  ((distinct t_1 ... t_n) or (eq t_1 t_2) .... or (eq t_n-1 t_n))
 * where d = (distinct t_1 ... t_n)
 */
static void create_distinct_lemma(egraph_t *egraph, composite_t *d) {
  bvar_t x;
  eterm_t t;
  ivector_t *v;
  cache_elem_t *e;

  assert(composite_kind(d) == COMPOSITE_DISTINCT);

  // check the cache first
  t = d->id;
  e = cache_get(&egraph->cache, DISTINCT_LEMMA, t, null_eterm);
  if (e->flag == NEW_CACHE_ELEM) {
    // lemma not previously expanded
    e->flag ++;

    // create the clause
    v = &egraph->aux_buffer;
    expand_distinct(egraph, composite_arity(d), d->child, v);

    x = egraph->terms.thvar[t];
    ivector_push(v, pos_lit(x));
    add_clause(egraph->core, v->size, v->data);

    // update statistics
    egraph->stats.nd_lemmas ++;
  }
}




/*
 * Get cache element for ackermann lemma (t1, t2)
 */
static cache_elem_t *cache_get_ackermann_lemma(cache_t *cache, eterm_t t1, eterm_t t2) {
  eterm_t aux;

  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }
  return cache_get(cache, ACKERMANN_LEMMA, t1, t2);
}


/*
 * Ackermann lemma: add the lemma
 *   (eq t_1 u_1) ... (eq t_n u_n) IMPLIES (eq (f t_1 ... t_n) (f u_1 ... u_n))
 * - c1 = (f t_1 ... t_n)
 * - c2 = (f u_1 ... u_n)
 */
static void create_ackermann_lemma(egraph_t *egraph, composite_t *c1, composite_t *c2) {
  uint32_t i, n;
  ivector_t *v;
  cache_elem_t *e;
  literal_t l;
  eterm_t b1, b2;
  thvar_t x1, x2;
  
  assert(composite_kind(c1) == composite_kind(c2) && composite_arity(c1) == composite_arity(c2));

  b1 = c1->id;
  b2 = c2->id;

  if (egraph_term_type(egraph, b1) == ETYPE_BOOL) {
    assert(egraph_term_type(egraph, b2) == ETYPE_BOOL);

    if (egraph_option_enabled(egraph, EGRAPH_DYNAMIC_BOOLACKERMANN) &&
	egraph->stats.boolack_lemmas < egraph->max_boolackermann) {
      
      /*
       * (f t_1 ... t_n) and (f u_1 ... u_n) are boolean.
       * Find boolean variables
       *   x1 <==> (f t_1 ... t_n) and x2 <==> (f u_1 ... u_n)
       * Add two clause:
       *  (eq t_1 u_1) AND ... AND (eq t_n u_n) AND x1 ==> x2
       *  (eq t_1 u_1) AND ... AND (eq t_n u_n) AND x2 ==> x1
       *
       * Before generating the clauses, check the number of hits for
       * the pair (b1, b2). Add the clauses if this reaches
       * boolack_threshold.
       */
      e = cache_get_ackermann_lemma(&egraph->cache, b1, b2);
      if (e->flag < egraph->boolack_threshold) {
	e->flag ++;
	if (e->flag == egraph->boolack_threshold) {
	  x1 = egraph_term_base_thvar(egraph, b1);
	  x2 = egraph_term_base_thvar(egraph, b2);
	  if (x1 != null_thvar && x2 != null_thvar) {
	    // generate the clause
	    v = &egraph->aux_buffer;
	    ivector_reset(v);
	    n = composite_arity(c1);
	    for (i=0; i<n; i++) {
	      l = egraph_make_aux_eq(egraph, c1->child[i], c2->child[i]);
	      if (l == null_literal) return; // quota exceeded: fail
	      if (l != true_literal) {
		ivector_push(v, not(l));
	      }
	    }
	    i = v->size;
	    // add x1 ==> x2
	    ivector_push(v, neg_lit(x1));
	    ivector_push(v, pos_lit(x2));	
	    add_clause(egraph->core, v->size, v->data);
	    // add x2 ==> x1
	    v->data[i] = neg_lit(x2);
	    v->data[i+1] = pos_lit(x1);
	    add_clause(egraph->core, v->size, v->data); 
	
	    egraph->stats.boolack_lemmas ++;
	  }
	}
      }
    }

  } else { 

    if (egraph_option_enabled(egraph, EGRAPH_DYNAMIC_ACKERMANN) &&
	egraph->stats.ack_lemmas < egraph->max_ackermann) {
    
      /*
       * Non-boolean case: add the clause 
       * (t_1 == u_1 and ... and t_n == u_n) ==> 
       *                (f t_1 .. t_n) == (f u_1 ... u_n)
       *
       * Generate the lemma if the number of hits for (b1, b2)
       * reaches ackermann_threshold.
       */
      e = cache_get_ackermann_lemma(&egraph->cache, b1, b2);
      if (e->flag < egraph->ackermann_threshold) {
	e->flag ++;
	if (e->flag == egraph->ackermann_threshold) {
	  v = &egraph->aux_buffer;
	  ivector_reset(v);
	  n = composite_arity(c1);
	  for (i=0; i<n; i++) {
	    l = egraph_make_aux_eq(egraph, c1->child[i], c2->child[i]);
	    if (l == null_literal) return; // aux_eq_quota exceeded
	    if (l != true_literal) {
	      ivector_push(v, not(l));
	    }
	  }
	  l = egraph_make_eq(egraph, pos_occ(b1), pos_occ(b2));
	  ivector_push(v, l);

#if 0
	  printf("---> ackermann lemma[%"PRIu32"]:\n", egraph->stats.ack_lemmas + 1);
	  n = v->size;
	  assert(n > 0);
	  if (n > 1) {
	    printf("(or ");
	  }
	  for (i=0; i<n; i++) {
	    printf(" ");
	    print_egraph_atom_of_literal(stdout, egraph, v->data[i]);
	  }
	  if (n > 1) {
	    printf(")");
	  }
	  printf("\n");
	  printf("      ");
	  print_eterm_def(stdout, egraph,  c1->id);
	  printf("      ");
	  print_eterm_def(stdout, egraph,  c2->id);
	  fflush(stdout);
#endif

	  add_clause(egraph->core, v->size, v->data);

	  // update statistics
	  egraph->stats.ack_lemmas ++;
	}
      }
    }
  }
}






/*********************************************************
 *  EQUALITY AND DISEQUALITIES BETWEEN THEORY VARIABLES  *
 ********************************************************/

/*
 * Propagate equality between two theory variables v1 and v2 in theory i
 * - v1 = theory var of c1
 * - v2 = theory var of c2
 * This is called when c1 and c2 are merged
 * - c1 remains root (and v1 remains visible in the egraph)
 * - c2 is no longer root after the merge (so v2 is no longer
 *   visible in the egraph).
 */
static void propagate_satellite_equality(egraph_t *egraph, etype_t i, thvar_t v1, thvar_t v2) {
  assert(i < NUM_SATELLITES && egraph->eg[i] != NULL);

  // call the merge function for theory i
  egraph->eg[i]->assert_equality(egraph->th[i], v1, v2);
}


/*
 * Propagate disequality between v1 and v2 in theory i
 */
static void propagate_satellite_disequality(egraph_t *egraph, etype_t i, thvar_t v1, thvar_t v2, composite_t *hint) {
  assert(i < NUM_SATELLITES && egraph->eg[i] != NULL);
  egraph->eg[i]->assert_disequality(egraph->th[i], v1, v2, hint);
}


/*
 * Propagate (distinct a[0] ... a[n-1]) to satellite solver i
 * - each a[k] is a theory variable in that solver
 * - hint is a composite term that implies (distinct a[0] ... a[n-1]):
 *   hint is (distinct t_0 ... t_p-1) asserted true, 
 *   and each a[i] is a theory variable attached to the class of some term t_j
 */
static void propagate_satellite_distinct(egraph_t *egraph, etype_t i, uint32_t n, thvar_t *a, composite_t *hint) {
  assert(i < NUM_SATELLITES && egraph->eg[i] != NULL);
  egraph->eg[i]->assert_distinct(egraph->th[i], n, a, hint);
}




/*
 * EQUALITIES BETWEEN TUPLES AND BOOLEAN VARIABLES
 */

/*
 * Tuple-equality propagation: implement the rule
 * (tuple t_1 ... t_n) == (tuple u_1 ... u_n) implies t_i == u_i
 * - v1: term with body[v1] = (tuple t_1 ... t_n)
 * - v2: term with body[v2] = (tuple u_1 ... u_n)
 */
static void propagate_tuple_equality(egraph_t *egraph, eterm_t v1, eterm_t v2) {
  composite_t *p1, *p2;
  uint32_t i, n;
  occ_t x1, x2;
  int32_t k;

  p1 = egraph_term_body(egraph, v1);
  p2 = egraph_term_body(egraph, v2);

  // if input is type correct, then p1 and p2 must have same arity
  // so p1->tag == p2->tag
  assert(composite_body(p1) && composite_body(p2) && p1->tag == p2->tag
	 && composite_kind(p1) == COMPOSITE_TUPLE);

  assert(egraph_equal_occ(egraph, pos_occ(v1), pos_occ(v2)));

  n = composite_arity(p1);
  x1 = pos_occ(v1);
  x2 = pos_occ(v2);
  for (i=0; i<n; i++) {
    if (! egraph_equal_occ(egraph, p1->child[i], p2->child[i])) {
      // (x1 == x2) implies p1->child[i] == p2->child[i]
      k = egraph_stack_push_eq(&egraph->stack, p1->child[i], p2->child[i]);
      egraph->stack.etag[k] = EXPL_EQ;
      egraph->stack.edata[k].t[0] = x1;
      egraph->stack.edata[k].t[1] = x2;
    }
  }
}


/*
 * When boolean variable v1 and v2 are merged into the same boolean class
 * - this means that either v1 == v2 or v1 == (not v2)
 * - if v1 == const_bvar, then v2 is now true or false.
 * - (v2 is never equal to const_bvar)
 */
static void propagate_boolean_equality(egraph_t *egraph, bvar_t v1, bvar_t v2) {
  atom_t *atm1, *atm2, *atm;
  smt_core_t *core;
  literal_t l;

  core = egraph->core;
  assert(core != NULL && bvar_has_atom(core, v1) && bvar_has_atom(core, v2));

  atm1 = get_bvar_atom(core, v1);
  atm2 = get_bvar_atom(core, v2);

  if (v1 == const_bvar) {
    atm = atm2;
    do {
      /*
       * atm->eterm is either true or false
       * assign the same value to atm->boolvar, with NULL as antecedent
       */
      assert(egraph_term_is_true(egraph, atm->eterm) || 
	     egraph_term_is_false(egraph, atm->eterm));

      if (bvar_value(core, atm->boolvar) == VAL_UNDEF) {
	l = mk_lit(atm->boolvar, egraph_term_is_false(egraph, atm->eterm));
	propagate_literal(core, l, NULL);
	egraph->stats.th_props ++;
      }

      atm = atm->next;
      
    } while (atm != atm2);
  }

  merge_atom_lists(atm1, atm2);
}



/*
 * Propagate equality between two theory variables v1 and v2
 * - v1 = theory var of c1
 * - v2 = theory var of c2
 * This is called when c1 and c2 are merged:
 * - c1 remains root (and v1 remains visible in the egraph)
 * - c2 is no longer root after the merge (so v2 is no longer
 *   visible in the egraph).
 */
static void propagate_thvar_equality(egraph_t *egraph, class_t c1, thvar_t v1, class_t c2, thvar_t v2) {
  etype_t i;

  assert(v1 != null_thvar && v2 != null_thvar && 
	 v1 == egraph_class_thvar(egraph, c1) &&
	 v2 == egraph_class_thvar(egraph, c2));

  i = egraph->classes.etype[c1];
  switch (i) {
  case ETYPE_INT:
  case ETYPE_REAL:
  case ETYPE_BV:
  case ETYPE_FUNCTION:
    propagate_satellite_equality(egraph, i, v1, v2);
    break;

  case ETYPE_BOOL:
    propagate_boolean_equality(egraph, v1, v2);
    break;

  case ETYPE_TUPLE:
    propagate_tuple_equality(egraph, v1, v2);
    break;

  default:
    assert(false);
  }
}



/*
 * Remove equality between two theory variables v1 and v2
 * - this is used only for boolean variables
 * - satellite solvers remove equalities or disequalities by backtracking
 * - for tuple equalities, there's nothing to undo 
 */
static void undo_thvar_equality(egraph_t *egraph, class_t c1, thvar_t v1, class_t c2, thvar_t v2) {
  smt_core_t *core;

  assert(v1 != null_thvar && v2 != null_thvar && 
	 v1 == egraph_class_thvar(egraph, c1) &&
	 v2 == egraph_class_thvar(egraph, c2));

  if (egraph->classes.etype[c1] == ETYPE_BOOL) {
    core = egraph->core;
    assert(core != NULL && bvar_has_atom(core, v1) && bvar_has_atom(core, v2));
    split_atom_lists(get_bvar_atom(core, v1), get_bvar_atom(core, v2));
  }
}




/*********************
 *  ATOM ASSIGNMENT  *
 ********************/

/*
 * Check for propagations when atom t --> (eq t1 t2) becomes true or false
 */
static void check_eq_atom(egraph_t *egraph, occ_t t, composite_t *atom) {
  occ_t t1, t2;
  class_t c1, c2;
  thvar_t v1, v2;
  int32_t k;
  etype_t i;

  t &= ~0x1; // make sure t = pos_occ(atom->id);
  assert(t == pos_occ(atom->id) && atom->tag == mk_eq_tag());

  if (egraph_occ_is_true(egraph, t)) {
    t1 = atom->child[0];
    t2 = atom->child[1];
    if (! egraph_equal_occ(egraph, t1, t2)) {
      // (eq t1 t2) == true implies (t1 == t2)
      k = egraph_stack_push_eq(&egraph->stack, t1, t2);
      egraph->stack.etag[k] = EXPL_EQ;
      egraph->stack.edata[k].t[0] = t;
      egraph->stack.edata[k].t[1] = true_occ;
#if TRACE
      printf("---> EGRAPH: equality ");
      print_occurrence(stdout, t1);
      printf(" == ");
      print_occurrence(stdout, t2);
      printf(" implied by ");
      print_composite(stdout, atom);
      printf(" == true\n");     
#endif
    }

  } else { 
    
    assert(egraph_occ_is_false(egraph, t));

    t1 = atom->child[0];
    t2 = atom->child[1];
    i = egraph_type(egraph, t1);

    if (i < NUM_SATELLITES ) {
      /*
       * Propagate the disequality to a satellite solver, if needed.
       */
      c1 = egraph_class(egraph, t1);
      v1 = egraph->classes.thvar[c1];
      c2 = egraph_class(egraph, t2);
      v2 = egraph->classes.thvar[c2];
      if (v1 != null_thvar && v2 != null_thvar) {
	propagate_satellite_disequality(egraph, i, v1, v2, atom);	
      }
      
    } else if (i == ETYPE_BOOL) {
      assert(egraph_type(egraph, t2) == ETYPE_BOOL);
      /*
       * Propagation rule: (eq t1 t2) == false implies (t1 == not t2)
       */
      if (! egraph_opposite_occ(egraph, t1, t2)) {
	k = egraph_stack_push_eq(&egraph->stack, t1, opposite_occ(t2));
	egraph->stack.etag[k] = EXPL_EQ;
	egraph->stack.edata[k].t[0] = t;
	egraph->stack.edata[k].t[1] = false_occ;
#if TRACE
	printf("---> EGRAPH: equality ");
	print_occurrence(stdout, t1);
	printf(" == ");
	print_occurrence(stdout, opposite_occ(t2));
	printf(" implied by ");
	print_composite(stdout, atom);
	printf(" == false\n");     
#endif
      }
    }
  }
}


/*
 * Check whether the assertion (distinct t_1 ... t_n) can 
 * be propagated to a satellite theory.
 * - atom = (distinct t_1 ... t_n)
 * - tau = the type of t_1
 */
static void check_satellite_distinct(egraph_t *egraph, etype_t tau, composite_t *atom) {
  ivector_t *v;
  uint32_t i, n;
  class_t c;
  thvar_t x;

  assert(tau < NUM_SATELLITES && composite_kind(atom) == COMPOSITE_DISTINCT);

  v = &egraph->aux_buffer;
  ivector_reset(v);

  // collect the theory variables in classes of t_1 ... t_n
  n = composite_arity(atom);
  for (i=0; i<n; i++) {
    c = egraph_class(egraph, atom->child[i]);
    x = egraph->classes.thvar[c];
    if (x != null_thvar) {
      ivector_push(v, x);
    }
  }

  if (v->size > 2) {
    propagate_satellite_distinct(egraph, tau, v->size, v->data, atom);
  } else if (v->size == 2) {
    propagate_satellite_disequality(egraph, tau, v->data[0], v->data[1], atom);
  }

}


/*
 * Assert (distinct t_1 ... t_n):
 * - assumes that this does not cause a conflict in the egraph. All children
 *   t_1 ... t_n must be in different classes.
 */
static void assert_distinct(egraph_t *egraph, composite_t *atom) {
  uint32_t k, i, n, j, m;
  uint32_t msk;
  class_t c, c1, c2;
  use_vector_t *v;
  composite_t *p;
  occ_t t1, t2;
  uint32_t *dmask;
  etype_t tau;

  assert(egraph->dtable.npreds < NDISTINCTS);

  // save data for backtracking
  undo_stack_push_distinct(&egraph->undo);

  // assign an index to atom in dtable
  k = egraph->dtable.npreds;
  egraph->dtable.distinct[k] = atom;
  egraph->dtable.npreds ++;

  dmask = egraph->classes.dmask;

  // update dmasks
  msk = ((uint32_t) 1) << k;
  n = composite_arity(atom);
  for (i=0; i<n; i++) {
    c = egraph_class(egraph, atom->child[i]);
    assert((dmask[c] & msk) == 0);
    dmask[c] |= msk;
  }

#if TRACE
  printf("---> EGRAPH: asserting ");
  print_composite(stdout, atom);
  printf("\n");
#endif

  // scan equality terms to check whether this makes them false
  for (i=0; i<n; i++) {
    c = egraph_class(egraph, atom->child[i]);
    v = egraph->classes.parents + c;
    m = v->last;
    for (j=0; j<m; j++) {
      p = v->data[j];
      if (valid_entry(p) && p->tag == mk_eq_tag()) {
	// p in v implies that p is in the congruence table,
	// so it was not false (or true) on entry to this function
	t1 = p->child[0];
	t2 = p->child[1];
	c1 = egraph_class(egraph, t1);
	c2 = egraph_class(egraph, t2);
	assert(c1 == c || c2 == c);

	if ((dmask[c1] & dmask[c2]) != 0) {
	  assert((dmask[c1] & dmask[c2]) == msk);
	  // p = (eq t1 t2) is false
	  add_diseq_implies_eq(egraph, p, false_occ, t1, t2, msk);
	  congruence_table_remove(&egraph->ctable, p);
	  detach_composite(p, egraph->terms.label, egraph->classes.parents);
	  assert(empty_entry(v->data[j]));
	  // save p  to restore it on backtracking
	  undo_stack_push_composite(&egraph->undo, p); 
	}

      }
    }
  }

  /*
   * Propagate to a satellite solver if needed
   */
  tau = egraph_type(egraph, atom->child[0]);
  if (tau < NUM_SATELLITES) {
    check_satellite_distinct(egraph, tau, atom);
  }

}




/*
 * Process atom (distinct t_1 ... t_n) after it's asserted true or false.
 * - return false if there's a conflict
 */
static bool check_distinct_atom(egraph_t *egraph, occ_t t, composite_t *atom) {
  t &= ~0x1;
  assert(t == pos_occ(atom->id) && composite_kind(atom) == COMPOSITE_DISTINCT);

  if (egraph_occ_is_true(egraph, t)) {
    // It's redundant to check for a conflict if atom is 
    // in the congruence table, but we don't know for sure.
    if (egraph_inconsistent_distinct(egraph, atom, &egraph->expl_vector)) {
      return false;
    } else {
      assert_distinct(egraph, atom);
    }

  } else {

    assert(egraph_occ_is_false(egraph, t));

    // important: egraph_inconsistent_not_distinct must be called
    // after egraph_check_distinct_false. 
    if (egraph_check_distinct_false(egraph, atom)) {
      return true;
    }

    if (egraph_inconsistent_not_distinct(egraph, atom, &egraph->expl_vector)) {
      return false;
    }

    // expand (not (distinct ...))
    create_distinct_lemma(egraph, atom);
  }

  return true;
}



/*
 * Function called when t is assigned to true or false
 * Check whether t is an atom and if so assert the atom.
 * - return false if a conflict is detected
 */
static bool check_atom_propagation(egraph_t *egraph, occ_t t) {
  composite_t *atom;

  assert(egraph_class(egraph, t) == bool_constant_class);

  atom = egraph_term_body(egraph, term_of_occ(t));  
  if (composite_body(atom)) {
    assert(atom != NULL);
    switch (composite_kind(atom)) {
    case COMPOSITE_EQ:
      check_eq_atom(egraph, t, atom);
      break;

    case COMPOSITE_DISTINCT:
      return check_distinct_atom(egraph, t, atom);

    default:
      // not an atom
      break;
    }
  }

  return true;  
}




/***********************
 *  MERGE TWO CLASSES  *
 **********************/

/*
 * Invert the edges on the branch from x to its root
 */
static void invert_branch(egraph_t *egraph, occ_t x) {
  eterm_t t;
  int32_t i, j;
  equeue_elem_t *eq;
  int32_t *edge;

  eq = egraph->stack.eq;
  edge = egraph->terms.edge;

  t = term_of_occ(x);
  i = null_edge;
  for (;;) {
    j = edge[t];
    edge[t] = i;
    if (j < 0) break; // j == null_edge
    t = edge_next(eq + j, t);
    i = j;
  }
}

/*
 * Scan use vector u. Store all equality terms into v
 */
static void collect_eqterms(use_vector_t *u, pvector_t *v) {
  uint32_t i, n;
  composite_t *p;

  pvector_reset(v);
  n = u->last;
  for (i=0; i<n; i++) {
    p = u->data[i];
    if (valid_entry(p) && p->tag == mk_eq_tag()) {
      pvector_push(v, p);
    }
  }
}

/*
 * Check all composites in v: they are all equalities
 * check whether they have become false (after change in dmask).
 */
static void check_false_eq(egraph_t *egraph, pvector_t *v) {
  uint32_t i;
  composite_t *p;
  occ_t t1, t2;
  class_t c1, c2;
  uint32_t *dmask, msk;

  dmask = egraph->classes.dmask;

  for (i=0; i<v->size; i++) {
    p = v->data[i];
    assert(p->tag == mk_eq_tag());
    t1 = p->child[0];
    t2 = p->child[1];
    c1 = egraph_class(egraph, t1);
    c2 = egraph_class(egraph, t2);
    msk = dmask[c1] & dmask[c2]; 
    if (msk != 0) {
      // t1 != t2 implies (eq t1 t2) == false
      add_diseq_implies_eq(egraph, p, false_occ, t1, t2, msk);
      congruence_table_remove(&egraph->ctable, p);
      detach_composite(p, egraph->terms.label, egraph->classes.parents);
      // save p so it can be restored on backtracking
      undo_stack_push_composite(&egraph->undo, p);
    }
  }  
}


/*
 * Process equality (t1 == t2): i = corresponding edge id
 * - egraph->stack.eq[i] is (t1 == t2)
 * - egraph->stack.etag[i] + egraph->stack.edata[i] == antecedent/explanation
 * 
 * - returned value: true means no inconsistency detected
 * - false means that a conflict was detected. The conflict literals are stored
 *   in egraph->expl_vector.
 */
static bool process_equality(egraph_t *egraph, occ_t t1, occ_t t2, int32_t i) {
  class_t c1, c2;
  int32_t aux;
  use_vector_t *v;
  uint32_t j, n, dmask;
  composite_t *p;
  elabel_t l;
  occ_t t;
  thvar_t v1, v2;

#if TRACE
  printf("\n---> EGRAPH: processing equality ");
  print_occurrence(stdout, t1);
  printf(" == ");
  print_occurrence(stdout, t2);
  printf("\n");
  if (egraph_term_is_composite(egraph, term_of_occ(t1))) {
    printf("---> ");
    print_eterm_def(stdout, egraph, term_of_occ(t1));
  }
  if (egraph_term_is_composite(egraph, term_of_occ(t2))) {
    printf("---> ");
    print_eterm_def(stdout, egraph, term_of_occ(t2));
  }
#endif

  // check whether (t1 == t2) is redundant
  if (egraph_equal_occ(egraph, t1, t2)) {
#if TRACE
    printf("---> redundant\n");
    fflush(stdout);
#endif
    return true;
  }

  // check whether it's inconsistent and if so construct the explanation
  if (egraph_inconsistent_edge(egraph, t1, t2, i, &egraph->expl_vector)) {
#if TRACE
    printf("---> conflict\n");
    fflush(stdout);
#endif

    if (egraph->stack.etag[i] == EXPL_BASIC_CONGRUENCE) {
      // store t1 t2 for local Ackermann generation 
      egraph->ack_left = t1;
      egraph->ack_right = t2;
    }

    return false;
  }

#if TRACE
  printf("---> merging ");
  print_label(stdout, egraph_label(egraph, t1));
  printf(" and ");
  print_label(stdout, egraph_label(egraph, t2));
  printf("\n");
  fflush(stdout);
#endif

  /*
   * Merge class of t2 into class of t1
   */
  c1 = egraph_class(egraph, t1);
  c2 = egraph_class(egraph, t2);

  assert(c1 != c2 && (egraph->classes.dmask[c1] & egraph->classes.dmask[c2]) == 0);

  // swap if necessary: we want c1 := union(c1, c2)
  // and we want to keep bool_constant_class as the root class
  if (c2 == bool_constant_class || 
      (c1 != bool_constant_class && egraph_class_nparents(egraph, c2) > egraph_class_nparents(egraph, c1))) {
    aux = t1; t1 = t2; t2 = aux;
    aux = c1; c1 = c2; c2 = aux;
  }

  // save t2 and its current label for backtracking
  undo_stack_push_merge(&egraph->undo, t2, egraph_label(egraph, t2));

  // update explanation tree: make t2 root of its tree
  invert_branch(egraph, t2);
  assert(egraph->terms.edge[term_of_occ(t2)] == null_edge);
  egraph->terms.edge[term_of_occ(t2)] = i; // new edge: t2 ---> t1

  /*
   * remove c2's parents from the congruence table
   * since their signature will change.
   */
  v = egraph->classes.parents + c2;
  n = v->last;
  for (j=0; j<n; j++) {
    p = v->data[j];
    if (valid_entry(p)) {
      // p is valid, i.e., it's in the congruence table
      congruence_table_remove(&egraph->ctable, p);
      // remove p from the parent vectors, except v
      separate_composite(p, egraph->terms.label, egraph->classes.parents, c2);
      assert(v->data[j] == p);
    }
  }

  /*
   * Assign new label to all terms in t2's class:
   * new label == current label of t1
   */
  l = egraph_label(egraph, t1);
  t = t2;
  do {
    egraph_set_label(egraph, t, l);
    t = egraph_next(egraph, t);
    assert(term_of_occ(t) != term_of_occ(t2) || t == t2);
  } while (t != t2);

  // update dmask of c1
  dmask = egraph->classes.dmask[c1];
  egraph->classes.dmask[c1] |= egraph->classes.dmask[c2];

  //  merge lists of terms: swap next[t1] and next[t2]
  t = egraph_next(egraph, t2);
  egraph_set_next(egraph, t2, egraph_next(egraph, t1));
  egraph_set_next(egraph, t1, t);

  /*
   * For propagation: if dmask[c1] has changed, some equality
   * terms in parents[c1] may have become false. Collect them
   * into egraph->cmp_vector.
   */
  if (egraph->classes.dmask[c1] != dmask) {
    collect_eqterms(egraph->classes.parents + c1, &egraph->cmp_vector);    
  }

  /*
   * Reprocess all composites in v == all parents of c2
   *
   * For backtracking, we keep all these composites in v
   * - if p remains a congruence root, it's kept as is in v
   * - if p is no longer a congruence root, it's kept as a marked 
   *   pointer in v.
   */
  for (j=0; j<n; j++) {
    p = v->data[j];
    if (valid_entry(p)) {
      if (composite_simplifies(egraph, p)) {
	// p is no longer in the congruence table
	// put a mark for backtracking
	mark_use_vector_entry(v, j);
      } else {
	// put p back into the use vectors
	// this adds p into c1's parent vector
	attach_composite(p, egraph->terms.label, egraph->classes.parents);
      }
    }
  }


  /*
   * Propagation 1: visit all equality terms in cmp_vector:
   * check whether they have become false.
   */
  if (egraph->classes.dmask[c1] != dmask) {
    check_false_eq(egraph, &egraph->cmp_vector);
  }

  /*
   * Propagation 2: if c1 == bool_constant_class, some atoms may
   * have become true or false.
   */
  if (c1 == bool_constant_class) {
    // atoms to visit = terms that were in t2's class.
    // now they are in the list t1->next ... --> t2
    t = t1;
    do {
      t = egraph_next(egraph, t);
      if (! check_atom_propagation(egraph, t)) {
	// conflict
	return false;
      }
    } while (t != t2);    
  }

  /*
   * Deal with theory variables of c1 and c2:
   * - if c2 has a theory var v2 but not c1, set v2 as theory var of c1
   * - if both have a theory variable, proagate equality (v1 == v2) to theory solvers
   * NOTE: this is also how we propagate tuple equalities
   */
  v2 = egraph->classes.thvar[c2];
  if (v2 != null_thvar) {
    v1 = egraph->classes.thvar[c1];
    if (v1 != null_thvar) {
      propagate_thvar_equality(egraph, c1, v1, c2, v2);
    } else {
      egraph->classes.thvar[c1] = v2;
    }
  }

  return true;
}






/***************************
 *  INTERNALIZATION START  *
 **************************/

/*
 * Set the presearch flag. Propagate the call to the satellite solvers
 */
void egraph_start_internalization(egraph_t *egraph) {
  uint32_t i;

  egraph->presearch = true;

  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      egraph->ctrl[i]->start_internalization(egraph->th[i]);
    }
  }
}



/******************
 *  START SEARCH  *
 *****************/

void egraph_start_search(egraph_t *egraph) {
  uint32_t i;

#if TRACE
  fprintf(stdout, "---> EGRAPH START_SEARCH [dlevel = %"PRIu32", decisions = %"PRIu64"]\n", 
	  egraph->decision_level, egraph->core->stats.decisions);
  fprintf(stdout, "\n=== EGRAPH TERMS ===\n");
  print_egraph_terms(stdout, egraph);
  fprintf(stdout, "\n");
#endif

  assert(egraph->core != NULL && egraph->decision_level == egraph->base_level);

  egraph->stats.eq_props = 0;
  egraph->stats.th_props = 0;
  egraph->stats.th_conflicts = 0;

  egraph->stats.final_checks = 0;
  egraph->stats.interface_eqs = 0;

  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      egraph->ctrl[i]->start_search(egraph->th[i]);
    }
  }

#if TRACE
  printf("\n=== EGRAPH TERMS ===\n");
  print_egraph_terms(stdout, egraph);
  printf("\n");
#endif

  egraph->presearch = false;
}



/*****************************
 *  INCREASE DECISION LEVEL  *
 ****************************/

static void egraph_open_decision_level(egraph_t *egraph) {
  uint32_t k;

  k = egraph->decision_level + 1;
  egraph->decision_level = k;
  if (egraph->stack.nlevels <= k) {
    increase_egraph_stack_levels(&egraph->stack);    
  }
  egraph->stack.level_index[k] = egraph->stack.top;

  if (egraph->undo.nlevels <= k) {
    increase_undo_stack_levels(&egraph->undo);
  }
  egraph->undo.level_index[k] = egraph->undo.top;

  // open new scope in arena
  arena_push(&egraph->arena);

#if TRACE
  printf("\n---> Egraph: increase decision level to %"PRIu32"\n", egraph->decision_level);
#endif
}


/*
 * Increase the decision level
 * - the propagation queue should be empty
 */
void egraph_increase_decision_level(egraph_t *egraph) {
  uint32_t i;

  assert(egraph->stack.prop_ptr == egraph->stack.top);

  egraph_open_decision_level(egraph);
  
  // forward to satellite solvers
  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      egraph->ctrl[i]->increase_decision_level(egraph->th[i]);
    }
  }
}


/**********
 *  PUSH  *
 *********/

void egraph_push(egraph_t *egraph) {
  uint32_t i;

  assert(egraph->decision_level == egraph->base_level);
  assert(egraph->terms.nterms == egraph->classes.nclasses);

  // save number of terms == number of classes, and propagation pointer
  egraph_trail_save(&egraph->trail_stack, egraph->terms.nterms, egraph->stack.prop_ptr);

  // mark cache content
  cache_push(&egraph->cache);

  // forward to the satellite solvers
  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      egraph->ctrl[i]->push(egraph->th[i]);
    }
  }

  // increase base level and decision level
  i = egraph->base_level + 1;
  egraph->base_level = i;
  egraph_open_decision_level(egraph);  

#if 0
  printf("\n*** EGRAPH PUSH EXIT ****\n");
  print_egraph_root_classes_details(stdout, egraph);
  print_egraph_congruence_roots(stdout, egraph);
#endif

}



/***********
 *  RESET  *
 **********/

/*
 * - remove all terms, classes, and atoms
 * - reset all stacks and tables
 * - set base_level and decision_level to 0
 */
void egraph_reset(egraph_t *egraph) {
  uint32_t i;

  egraph->base_level = 0;
  egraph->decision_level = 0;
  egraph->ndistincts = 0;
  egraph->is_high_order = false;

  reset_egraph_stats(&egraph->stats);
  egraph->ack_left = null_occurrence;
  egraph->ack_right = null_occurrence;

  reset_class_table(&egraph->classes);
  reset_eterm_table(&egraph->terms);
  reset_egraph_stack(&egraph->stack);
  reset_undo_stack(&egraph->undo);
  reset_distinct_table(&egraph->dtable);
  reset_congruence_table(&egraph->ctable);
  reset_egraph_trail(&egraph->trail_stack);

  egraph_free_const_htbl(egraph);
  reset_int_htbl(&egraph->htbl);
  reset_objstore(&egraph->atom_store);  // delete all atoms
  reset_cache(&egraph->cache);
  arena_reset(&egraph->arena);

  if (egraph->app_partition != NULL) {
    delete_ptr_partition(egraph->app_partition);
    safe_free(egraph->app_partition);
    egraph->app_partition = NULL;
  }

  egraph_init_constant(egraph);

  // model-building objects
  reset_egraph_model(&egraph->mdl);

  // forward reset to the satellite solvers
  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      egraph->ctrl[i]->reset(egraph->th[i]);
    }
  }
}





/*******************
 *  BACKTRACKING   *
 ******************/

/*
 * Undo operation: remove the last (distinct ...)
 */
static void undo_distinct(egraph_t *egraph) {
  uint32_t k, msk, i, n;
  uint32_t *dmask;
  composite_t *d;
  class_t c;

  assert(egraph->dtable.npreds > 1);

  k = egraph->dtable.npreds - 1;
  d = egraph->dtable.distinct[k];
  egraph->dtable.npreds = k;
  
  // clear bit k in dmasks
  dmask = egraph->classes.dmask;
  msk = ~(((uint32_t) 1) << k);

  assert(d != NULL && composite_kind(d) == COMPOSITE_DISTINCT);
  n = composite_arity(d);
  for (i=0; i<n; i++) {
    c = egraph_class(egraph, d->child[i]);
    assert((dmask[c] & ~msk) == ~msk);
    dmask[c] &= msk;
  }
}


/*
 * Put composite cmp back into its parents vector
 * and into the congruence table.
 */
static void restore_composite(egraph_t *egraph, composite_t *cmp) {
#ifndef NDEBUG
  // cmp->hash should be valid 
  signature_composite(cmp, egraph->terms.label, &egraph->sgn);
  assert(cmp->hash == hash_signature(&egraph->sgn));
#endif
  congruence_table_add(&egraph->ctable, cmp);
  attach_composite(cmp, egraph->terms.label, egraph->classes.parents);
}


/*
 * Undo merge: t2 = saved occurrence, l2 = saved label
 * - let i = edge[t2] then egraph->stack.eq[i] is either <t1, t2> or <t2, t1>
 * - undo merge is the converse of process_equality(t1, t2, i):
 */
static void undo_merge(egraph_t *egraph, occ_t t2, elabel_t l2) {
  class_t c1, c2;
  occ_t t1, t;
  int32_t i, n;
  use_vector_t *v;
  composite_t *p;
  elabel_t *label;

  c1 = egraph_class(egraph, t2);
  c2 = class_of(l2);

  i = egraph->terms.edge[term_of_occ(t2)];
  assert(0 <= i && i < egraph->stack.top);

  t1 = edge_next_occ(egraph->stack.eq + i, t2);
  assert(egraph_class(egraph, t1) == c1);

  /*
   * parents[c2] stores composites that need to be reinserted
   * in ctable after relabeling.
   * - marked elements in parents[c2] --> not currenctly in ctable
   * - valid elements in parents[c2] --> still in ctable
   * First loop: remove all composites in parents[c2] from ctable,
   * remove mark from the marked elements.
   */
  label = egraph->terms.label;
  v = egraph->classes.parents + c2;
  n = v->last;
  for (i=0; i<n; i++) {
    p = v->data[i];
    if (valid_entry(p)) {
      congruence_table_remove(&egraph->ctable, p);
      detach_composite(p, label, egraph->classes.parents);
    } else if (marked_entry(p)) {
      unmark_use_vector_entry(v, i);
    }
  }

  /*
   * class c1 is a circular list of the form
   * t1 --> x .... --> t2 --> y ... --> t1
   * we split it in into two circular sublists:
   * t2 --> x ... --> t2  and t1 --> y ... -> t1
   */
  t = egraph_next(egraph, t2);
  egraph_set_next(egraph, t2, egraph_next(egraph, t1));
  egraph_set_next(egraph, t1, t);

  // restore label l2 to t2 and all terms in its list
  t = t2;
  do {
    egraph_set_label(egraph, t, l2);
    t = egraph_next(egraph, t);
    assert(term_of_occ(t) != term_of_occ(t2) || t == t2);
  } while (t != t2);

  // restore dmask of c1
  egraph->classes.dmask[c1] &= ~egraph->classes.dmask[c2];

  // remove edge from t2 --> t1 then restore branch t2 ---> c2.root
  egraph->terms.edge[term_of_occ(t2)] = null_edge;
  invert_branch(egraph, egraph->classes.root[c2]);

  /*
   * Put parents[c2] back into ctable
   */
  for (i=0; i<n; i++) {
    p = v->data[i];
    assert(valid_entry(p) || empty_entry(p));
    if (valid_entry(p)) {
      signature_composite(p, label, &egraph->sgn);
      p->hash = hash_signature(&egraph->sgn);
      // p should be a congruence root
      assert(congruence_table_find(&egraph->ctable, &egraph->sgn, label) == NULL_COMPOSITE);

      congruence_table_add(&egraph->ctable, p);
      clear_use_vector_entry(v, i); // required for attach_composite
      attach_composite(p, label, egraph->classes.parents);
    }
  }

  /*
   * Restore theory variables:
   * if thvar[c1] == thvar[c2] != null, then we restore thvar[c1] to null
   * if thvar[c1] != thvar[c2] and thvar[c2] != null, undo_thvar_equality
   * does any extra processing needed.
   *
   * Exception: if c1 == bool_constant_class, it may happen that
   * thvar[c1] == thvar[2] == const_bvar: but we don't want to 
   * set thvar[c1] to null_thvar.
   */ 
  if (egraph->classes.thvar[c2] != null_thvar) {
    assert(egraph->classes.thvar[c1] != null_thvar);
    if (egraph->classes.thvar[c1] == egraph->classes.thvar[c2])  {
      if (c1 != bool_constant_class) {
	egraph->classes.thvar[c1] = null_thvar;
      }
    } else {
      undo_thvar_equality(egraph, c1, egraph->classes.thvar[c1], c2, egraph->classes.thvar[c2]);
    }
  }

} 


/*
 * Remove a congruence root from the congruence table and use vectors.
 * - at the time this function is called, p should be in a singleton
 * class c (the class created when p was activated).
 */
static void deactivate_congruence_root(egraph_t *egraph, composite_t *p) {
#ifndef NDEBUG
  class_t c;
  eterm_t t;
#endif
  elabel_t *label;

  label = egraph->terms.label;

#ifndef NDEBUG
  t = p->id;
  c = egraph_term_class(egraph, t);
  
  // check that p->hash is valid
  signature_composite(p, label, &egraph->sgn);
  assert(p->hash == hash_signature(&egraph->sgn));

  // check that p is in ctable
  assert(congruence_table_find(&egraph->ctable, &egraph->sgn, label) == p);

  // t should be root of c and c should contain t only
  assert(egraph->classes.root[c] == pos_occ(t));
  assert(egraph->terms.next[t] == pos_occ(t));
#endif

  congruence_table_remove(&egraph->ctable, p);
  detach_composite(p, label, egraph->classes.parents);
}


/*
 * Generate the ackermann lemma for term occurrences t1 and t2
 */
static void egraph_gen_ackermann_lemma(egraph_t *egraph, occ_t t1, occ_t t2) {
  composite_t *c1, *c2;

  c1 = egraph_term_body(egraph, term_of_occ(t1));
  c2 = egraph_term_body(egraph, term_of_occ(t2));
  create_ackermann_lemma(egraph, c1, c2);
}


/*
 * Backtrack to back_level
 * (we need to isolate this because it's used in pop);
 */
static void egraph_local_backtrack(egraph_t *egraph, uint32_t back_level) {
  uint32_t i, k;
  unsigned char *utag;
  undo_t *udata;
  uint32_t n;

  assert(egraph->base_level <= back_level && back_level < egraph->decision_level);
  
#if TRACE
  printf("---> EGRAPH:   Backtracking to level %"PRIu32"\n\n", back_level);
#endif


  /*
   * Generate ackermann lemmas if enabled: this must be done first
   */
  if (egraph->ack_left != null_occurrence && 
      egraph_option_enabled(egraph, EGRAPH_DYNAMIC_ACKERMANN | EGRAPH_DYNAMIC_BOOLACKERMANN)) {
    assert(egraph->ack_right != null_occurrence);
    egraph_gen_ackermann_lemma(egraph, egraph->ack_left, egraph->ack_right);
    egraph->ack_left = null_occurrence;
    egraph->ack_right = null_occurrence;
  }


  // undo everything in undo_stack[k ... top-1]
  k = egraph->undo.level_index[back_level + 1];
  i = egraph->undo.top;
  utag = egraph->undo.tag;
  udata = egraph->undo.data;
  while (i > k) {
    i --;
    switch (utag[i]) {
    case UNDO_MERGE:
      undo_merge(egraph, udata[i].merge.saved_occ, udata[i].merge.saved_label);
      break;

    case UNDO_DISTINCT:
      undo_distinct(egraph);
      break;

    case UNDO_SIMPLIFY:
      restore_composite(egraph, udata[i].ptr);
      break;

    // store terms to reanalyze into reanalyze_vector
    case REANALYZE_CONGRUENCE_ROOT:
      deactivate_congruence_root(egraph, udata[i].ptr);
      pvector_push(&egraph->reanalyze_vector, udata[i].ptr);
      break;

    case REANALYZE_COMPOSITE:
      pvector_push(&egraph->reanalyze_vector, udata[i].ptr);
      break;

    default:
      assert(false);
    }
  }
  assert(i == k);
  egraph->undo.top = k;  

  // Cleanup the propagation stack
  k = egraph->stack.level_index[back_level + 1];
  egraph->stack.top = k;
  egraph->stack.prop_ptr = k;

  // delete all temporary data in the arena
  n = egraph->decision_level;
  do {
    arena_pop(&egraph->arena);
    n --;
  } while (n > back_level);
  
  egraph->decision_level = back_level;
}


/*
 * Full backtrack: egraph + all satellite solvers
 */
void egraph_backtrack(egraph_t *egraph, uint32_t back_level) {
  uint32_t i;

  egraph_local_backtrack(egraph, back_level);

  // forward to the satellite solvers
  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      egraph->ctrl[i]->backtrack(egraph->th[i], back_level);
    }
  }
}





/*********
 *  POP  *
 ********/

/*
 * Delete composite p
 * - remove it from the congruence table and parent vectors
 *   if it's a congruence root
 * - also remove the corresponding record from the htbl
 */
static void delete_composite(egraph_t *egraph, composite_t *p) {
  elabel_t *label;
  uint32_t h;

  label = egraph->terms.label;

  // compute p->hash
  signature_composite(p, label, &egraph->sgn);
  p->hash = hash_signature(&egraph->sgn);

  if (congruence_table_remove_if_present(&egraph->ctable, p)) {
    detach_composite(p, label, egraph->classes.parents);
  }

  // hash code used in hash-consing
  h = hash_composite(p);
  int_htbl_erase_record(&egraph->htbl, h, p->id);

  safe_free(p);
}


/*
 * Cleanup the term table
 * - remove terms of id n to nterms - 1
 */
static void restore_eterms(egraph_t *egraph, uint32_t n) {
  composite_t *cmp;
  eterm_t t;
  thvar_t x;
  atom_t *atom;

  t = egraph->terms.nterms;  
  assert(t >= n);

  while (t > n) {
    t --;
    cmp = egraph_term_body(egraph, t);
    if (composite_body(cmp)) {
      delete_composite(egraph, cmp);
    } else if (constant_body(cmp)) {
      egraph_delete_constant(egraph, t);
    }

    x = egraph_term_base_thvar(egraph, t);
    assert(x == egraph_term_thvar(egraph, t));
    if (x != null_thvar && egraph_term_type(egraph, t) == ETYPE_BOOL) {
      // remove atom if there's one
      atom = get_egraph_atom_for_bvar(egraph, x);
      if (atom != NULL) {
	delete_egraph_atom(egraph, atom);
      }
    }
  }

  egraph->terms.nterms = n;  
}


/*
 * Cleanup the class table: remove class of ids n to nclasses - 1
 */
static void restore_classes(egraph_t *egraph, uint32_t n) {
  class_t c;

  c = egraph->classes.nclasses;
  assert(c >= n);

  while (c > n) {
    c --;
    free_parents(&egraph->classes, c);
  }
  egraph->classes.nclasses = n;
}


/*
 * Return to the previous base_level
 */
void egraph_pop(egraph_t *egraph) {
  egraph_trail_t *trail;
  uint32_t i;

#if 0
  printf("*** EGRAPH POP ENTRY ****\n");
  print_egraph_root_classes_details(stdout, egraph);
  print_egraph_congruence_roots(stdout, egraph);
#endif

  assert(egraph->base_level > 0 && egraph->base_level == egraph->decision_level);

  // decrease base_level then backtrack
  egraph->ack_left = null_occurrence;
  egraph->ack_right = null_occurrence;
  egraph->base_level --;
  egraph_local_backtrack(egraph, egraph->base_level);

  // clear the high-order flag
  egraph->is_high_order = false;
  
  // all dynamic terms will be deleted 
  // so we must empty reanalyze vector
  pvector_reset(&egraph->reanalyze_vector);

  // remove all terms and classes of id >= trail->nterms
  trail = egraph_trail_top(&egraph->trail_stack);
  restore_eterms(egraph, trail->nterms);
  restore_classes(egraph, trail->nterms);

  // restore the propagation pointer
  egraph->stack.prop_ptr = trail->prop_ptr;

  // cleanup the cache
  cache_pop(&egraph->cache);

  // remove top trail element
  egraph_trail_pop(&egraph->trail_stack);

  // forward pop to the satellite solvers
  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      egraph->ctrl[i]->pop(egraph->th[i]);
    }
  }  

#if 0
  printf("\n*** EGRAPH POP: EXIT ****\n");
  print_egraph_root_classes_details(stdout, egraph);
  print_egraph_congruence_roots(stdout, egraph);
#endif

}



/*****************
 *  PROPAGATION  *
 ****************/

/*
 * Reactivate the terms in reanalyze_vector
 * - this must be called after backtracking and before processing any equality
 */
static void egraph_reactivate_dynamic_terms(egraph_t *egraph) {
  pvector_t *v;
  composite_t *p;
  uint32_t i, n;

  v = &egraph->reanalyze_vector;
  n = v->size;
  for (i=0; i<n; i++) {
    p = v->data[i];
    assert(composite_body(p));
    egraph_activate_composite(egraph, p);
  }
  pvector_reset(v);
}


/*
 * Propagation via equality propagation queue.
 * Return false if a conflict is detected, true otherwise.
 * If there's a conflict, it is stored (as a conjunction of literals) in egraph->expl_vector.
 */
static bool egraph_internal_propagation(egraph_t *egraph) {
  equeue_elem_t *e;
  uint32_t i;

  // reactivate any composite in the reanalyze_vector
  if (egraph->reanalyze_vector.size > 0) {
    egraph_reactivate_dynamic_terms(egraph);
  }

  // process the equality queue
  i = egraph->stack.prop_ptr;
  while (i < egraph->stack.top) {
    e = egraph->stack.eq + i;
    if (! process_equality(egraph, e->lhs, e->rhs, i)) {
      egraph->stack.prop_ptr = i;
      return false;
    }
    i ++;
  }
  egraph->stack.prop_ptr = i;

  return true;
}


/*
 * Full propagation: in egraph and satellite solvers
 * Return false if there's a conflict, true otherwise.
 * If the conflict is in the egraph, report it to the core.
 */
bool egraph_propagate(egraph_t *egraph) {
  uint32_t i;
  ivector_t *conflict;

#if TRACE
  printf("---> EGRAPH PROPAGATE [dlevel = %"PRIu32", decisions = %"PRIu64"]\n", 
	 egraph->decision_level, egraph->core->stats.decisions);
#endif

  if (! egraph_internal_propagation(egraph)) {
    /*
     * Egraph conflict:
     * the conflict is in egraph->expl_vector, in the form "not (l1 and .... and l_n)"
     * we need to turn this into the clause "(not l_1) or ... or (not l_n)"
     * and add the end marker.
     */
    conflict = &egraph->expl_vector;
    for (i=0; i<conflict->size; i++) {
      conflict->data[i] = not(conflict->data[i]);
    }
    ivector_push(conflict, null_literal); // end marker
    record_theory_conflict(egraph->core, conflict->data);

    egraph->stats.th_conflicts ++;

    return false;
  }

  // go through all the satellite solvers
  for (i=0; i<NUM_SATELLITES; i++) {
    if (egraph->ctrl[i] != NULL) {
      if (! egraph->ctrl[i]->propagate(egraph->th[i])) {
	return false;
      }
    }
  }

  return true;
}



/***************************
 *  INTERFACE EQUALITIES   *
 **************************/

/*
 * Simpler version of make_eq: does not check whether 
 * t1 and t2 are known to be equal or distinct.
 *
 * In particular, this function does not call the theory's check_diseq
 * function to avoid circularity.
 */
literal_t egraph_make_simple_eq(egraph_t *egraph, occ_t t1, occ_t t2) {
  occ_t aux;
  eterm_t t;

  assert(t1 != t2);

  // normalize
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  t = egraph_eq_term(egraph, t1, t2);
  return egraph_term2literal(egraph, t);  
}



/**********************
 *  HIGH-ORDER TERMS  *
 *********************/

/*
 * Check whether child i of p is a function
 */
static inline bool composite_child_is_function(egraph_t *egraph, composite_t *cmp, uint32_t i) {
  return egraph_term_is_function(egraph, term_of_occ(composite_child(cmp, i)));
}

/*
 * Check whether one child of p is a function:
 * - scan chidren from i to p's arity (i=0 or i=1 to skip the first child)
 */
static bool composite_has_function_child(egraph_t *egraph, composite_t *cmp, uint32_t i) {
  uint32_t n;

  n = composite_arity(cmp);
  while (i < n) {
    if (composite_child_is_function(egraph, cmp, i)) {
      return true;
    }
    i ++;
  }
  return false;
}

/*
 * Check whether composite cmp is high order:
 * - return true if some of cmp's children are function terms
 */
static bool composite_is_high_order(egraph_t *egraph, composite_t *cmp) {
  switch (composite_kind(cmp)) {
  case COMPOSITE_APPLY:
  case COMPOSITE_UPDATE:
    return composite_has_function_child(egraph, cmp, 1);
  case COMPOSITE_TUPLE:
    return composite_has_function_child(egraph, cmp, 0);
  case COMPOSITE_EQ:
    // (eq u v): both u and v are functions or neither is
    return composite_child_is_function(egraph, cmp, 0);
  case COMPOSITE_ITE:
    // (ite c u v): both u and v are functions or neither is
    return composite_child_is_function(egraph, cmp, 1);
  case COMPOSITE_DISTINCT:
    // (distinct u_1 ... u_n) all children are functions or none
    return composite_child_is_function(egraph, cmp, 0);
  case COMPOSITE_OR:
  default:
    return false;
  }
}


/*
 * Check whether there's a high order term in the egraph
 */
static bool egraph_has_high_order_terms(egraph_t *egraph) {
  composite_t *cmp;
  uint32_t i, n;

  n = egraph_num_terms(egraph);
  for (i=0; i<n; i++) {
    cmp = egraph_term_body(egraph, i);
    if (composite_body(cmp) && composite_is_high_order(egraph, cmp)) {
      return true;
    }
  }
  return false;
}


/*
 * Check for high-order terms then cache the result in egraph->is_high_order
 */
static bool egraph_is_high_order(egraph_t *egraph) {
  bool h;

  h = egraph->is_high_order;
  if (!h) {
    h = egraph_has_high_order_terms(egraph);
    egraph->is_high_order = h;
  }
  return h;
}



/*****************************************************
 *  EXPERIMENTAL: EGRAPH GENERATES INTERFACE LEMMAS  *
 ****************************************************/

/*
 * Prepare the satellite models for the arithmetic and bitvector theories
 */
static void egraph_prepare_models(egraph_t *egraph) {
  if (egraph->ctrl[ETYPE_REAL] != NULL) {
    assert(egraph->eg[ETYPE_REAL] != NULL);
    egraph->eg[ETYPE_REAL]->prepare_model(egraph->th[ETYPE_REAL]);
  }
  if (egraph->ctrl[ETYPE_BV] != NULL) {
    assert(egraph->eg[ETYPE_BV] != NULL);
    egraph->eg[ETYPE_BV]->prepare_model(egraph->th[ETYPE_BV]);
  }    
}


/*
 * Release the satellite models
 */
static void egraph_release_models(egraph_t *egraph) {
  if (egraph->ctrl[ETYPE_REAL] != NULL) {
    assert(egraph->eg[ETYPE_REAL] != NULL);
    egraph->eg[ETYPE_REAL]->release_model(egraph->th[ETYPE_REAL]);
  }
  if (egraph->ctrl[ETYPE_BV] != NULL) {
    assert(egraph->eg[ETYPE_BV] != NULL);
    egraph->eg[ETYPE_BV]->release_model(egraph->th[ETYPE_BV]);
  }
}



/*
 * Literal that implies (cmp == true/false) 
 * - cmp must have boolean type and must be true or false
 * - if cmp is asserted as an axiom. then we return true_literal
 * - otherwise, there's a Boolean variable v such that v <=> (cmp == true)
 * - if cmp is false, we return, (not v)
 *   if cmp is true, we return v
 */
static literal_t literal_for_composite(egraph_t *egraph, composite_t *cmp) {
  eterm_t t;
  thvar_t v;
  literal_t l;

  t = cmp->id;
  v = egraph_term_base_thvar(egraph, t);

  assert(egraph_term_type(egraph, t) == ETYPE_BOOL && 
	 egraph_term_class(egraph, t) == bool_constant_class);

  /*
   * If v == null_thvar, we want l = true_literal
   * since t or (not t) was asserted as an axiom.
   * Otherwise, the literal attached to t is pos_lit(v)
   */
  l = true_literal;
  if (v != null_thvar) {
    if (egraph_term_is_true(egraph, t)) {
      l = pos_lit(v);
    } else {
      assert(egraph_term_is_false(egraph, t));
      l = neg_lit(v);
    }
  }

  return l;
}


/*
 * Check whether we need an interface lemma for cmp = (eq t1 t2)
 * - cmp is known to be false when this is called.
 * - return 1 if an interface lemma is generated, 0 otherwise
 */
static uint32_t check_diseq_interface_lemma(egraph_t *egraph, composite_t *cmp) {
  void *satellite;
  th_egraph_interface_t *interface;
  occ_t t1, t2;
  thvar_t x1, x2;
  literal_t l;

  assert(composite_kind(cmp) == COMPOSITE_EQ && egraph_term_is_false(egraph, cmp->id));

  t1 = cmp->child[0];
  t2 = cmp->child[1];
  x1 = egraph_base_thvar(egraph, t1);
  x2 = egraph_base_thvar(egraph, t2);

  if (x1 == null_thvar || x2 == null_thvar) {
    return 0;
  }

  switch (egraph_type(egraph, t1)) {
  case ETYPE_INT:
  case ETYPE_REAL:
    satellite = egraph->th[ETYPE_REAL];
    interface = egraph->eg[ETYPE_REAL];
    break;

  case ETYPE_BV:
    satellite = egraph->th[ETYPE_BV];
    interface = egraph->eg[ETYPE_BV];
    break;

  default:
    return 0;
  }

  if (interface->equal_in_model(satellite, x1, x2)) {
    // conflict between egraph and salellite model: create a lemma
#if TRACE
    printf("---> EGRAPH: interface lemma for ");
    print_eterm_def(stdout, egraph, cmp->id);
    printf("     label[");
    print_occurrence(stdout, t1);
    printf("] = ");
    print_label(stdout, egraph_label(egraph, t1));
    printf("\n");
    printf("     label[");
    print_occurrence(stdout, t2);
    printf("] = ");
    print_label(stdout, egraph_label(egraph, t2));
    printf("\n");
#endif
    l = literal_for_composite(egraph, cmp);
    assert(literal_value(egraph->core, l) == VAL_TRUE);
    interface->gen_interface_lemma(satellite, l, x1, x2, true);
    return 1;
  } 
  
  return 0;
}



/*
 * Check whether we need interface lemma(s) for cmp = (distinct t1 t2 ... t_n)
 * - cmp is known to be true when this is called.
 * - return the number of an interface lemma is generated
 */
static uint32_t check_distinct_interface_lemma(egraph_t *egraph, composite_t *cmp, uint32_t max_eq) {
  void *satellite;
  th_egraph_interface_t *interface;
  uint32_t i, j, n, neqs;
  occ_t t1, t2;
  thvar_t x1, x2;
  literal_t l;

  assert(composite_kind(cmp) == COMPOSITE_DISTINCT && egraph_term_is_true(egraph, cmp->id));

  neqs = 0;

  switch (egraph_type(egraph, cmp->child[0])) {
  case ETYPE_INT:
  case ETYPE_REAL:
    satellite = egraph->th[ETYPE_REAL];
    interface = egraph->eg[ETYPE_REAL];
    break;

  case ETYPE_BV:
    satellite = egraph->th[ETYPE_BV];
    interface = egraph->eg[ETYPE_BV];
    break;

  default:
    goto done;
  }


  l = literal_for_composite(egraph, cmp);
  assert(literal_value(egraph->core, l) == VAL_TRUE);	

  n = composite_arity(cmp);
  for (i=0; i<n; i++) {
    t1 = cmp->child[i];
    x1 = egraph_base_thvar(egraph, t1);

    for (j=i+1; j<n; j++) {
      t2 = cmp->child[j];
      x2 = egraph_base_thvar(egraph, t2);

      if (interface->equal_in_model(satellite, x1, x2)) {
	// conflict between egraph and salellite model: create a lemma
#if TRACE
	printf("---> EGRAPH: interface lemma for ");
	print_eterm_id(stdout, t1);
	printf(" ");
	print_eterm_id(stdout, t2);
	printf("\n");
	printf("     ");
	print_eterm_def(stdout, egraph, cmp->id);
#endif
	interface->gen_interface_lemma(satellite, l, x1, x2, false);
	neqs ++;
	if (neqs >= max_eq) goto done;
      }
    }
  }

 done:
  return neqs;
}



/*
 * Generate direct conflict lemmas:
 * - search for terms t1 and t2 such that t1 and t2 must be different   
 *   in the Egraph but have equal values in the theory model
 * - t1 and t2 must be distinct in the Egraph either because
 *    (eq t1 t2) is false, or because (distinct .. t1 ... t2 ...) is true
 * - for each such pair: call the solver's interface lemma generation
 *   function.
 * - stop once max_eqs is reached.
 * - return the total number of lemmas generated
 */
static uint32_t egraph_direct_interface_lemmas(egraph_t *egraph, uint32_t max_eqs) {
  eterm_table_t *terms;
  composite_t *cmp;
  uint32_t i, n, neqs;

  neqs = 0;

  terms = &egraph->terms;
  n = terms->nterms;

  for (i=1; i<n; i++) {
    cmp = terms->body[i];
    if (composite_body(cmp)) {
      switch (composite_kind(cmp)) {
      case COMPOSITE_EQ:
	if (terms->label[i] == false_label &&
	    congruence_table_is_root(&egraph->ctable, cmp, terms->label)) {
	  neqs += check_diseq_interface_lemma(egraph, cmp);
	  if (neqs >= max_eqs) goto done;
	}
	break;

      case COMPOSITE_DISTINCT:
	if (terms->label[i] == true_label) {
	  neqs += check_distinct_interface_lemma(egraph, cmp, max_eqs - neqs);
	  if (neqs >= max_eqs)  goto done;
	}
	break;

      default:
	break;
      }
    }
  }

 done:
  return neqs;
}



/*
 * INDIRECT LEMMAS
 */

/*
 * Given two terms t1 and t2 such that:
 * - t1 and t2 are distinct in the Egraph
 * - t1 has theory variable x1 
 * - t2 has theory variable x2
 * - x1 and x2 have the same value in a theory solver
 * - merging t1 and t2 could cause a conflict by congruence closure
 * Then we generate an interface lemma for t1 and t2:
 *   (not (eq t1 t2)) => (x1 != x2 in the theory)
 *
 * To check for possible conflicts, we use the following rule:
 * - t1 and t2 may conflict if there are two terms 
 *      u1 := (f ... t1 ...) 
 *  and u2 := (f ... t2 ...) that can't be merged in the 
 *  current models: either becuase u1 and u2 don't have theory 
 *  variables and are in distinct Egraph classes, or they have theory 
 *  variables that have different values in the relevant theory solvers.
 */


/*
 * Check whether terms u1 and u2 can't be merged
 */
static bool non_mergeable_in_models(egraph_t *egraph, eterm_t u1, eterm_t u2) {
  void *satellite;
  th_egraph_interface_t *interface;
  thvar_t x1, x2;

  if (egraph_equal_terms(egraph, u1, u2)) {
    return false; // already merged
  }

  x1 = egraph_term_base_thvar(egraph, u1);
  x2 = egraph_term_base_thvar(egraph, u2);

  if (x1 == null_thvar || x2 == null_thvar) {
    return true;
  }

  switch (egraph_term_type(egraph, u1)) {
  case ETYPE_INT:
  case ETYPE_REAL:
    satellite = egraph->th[ETYPE_REAL];
    interface = egraph->eg[ETYPE_REAL];
    break;

  case ETYPE_BV:
    satellite = egraph->th[ETYPE_BV];
    interface = egraph->eg[ETYPE_BV];
    break;

  default:
    return true;
  }

  return !interface->equal_in_model(satellite, x1, x2);
}


/*
 * Check for an interface equality involving cmp1 and cmp2
 * - both composites must be of the form (apply f ...)
 * - return 0 if no interface lemma is generated, 1 otherwise
 */
static uint32_t check_interface_lemma_for_applies(egraph_t *egraph, composite_t *cmp1, composite_t *cmp2) {
  void *satellite;
  th_egraph_interface_t *interface;
  uint32_t i, n;
  occ_t t1, t2;
  thvar_t x1, x2;
  literal_t eq;

  assert(composite_kind(cmp1) == COMPOSITE_APPLY && 
	 composite_kind(cmp2) == COMPOSITE_APPLY &&
	 composite_arity(cmp1) == composite_arity(cmp2) &&
	 non_mergeable_in_models(egraph, cmp1->id, cmp2->id));

  interface = NULL;  // prevent GCC warning
  satellite = NULL;  // prevent GCC warning

  n = composite_arity(cmp1);
  for (i=1; i<n; i++) {
    t1 = composite_child(cmp1, i);
    t2 = composite_child(cmp2, i);

    if (egraph_class(egraph, t1) != egraph_class(egraph, t2)) {
      x1 = egraph_base_thvar(egraph, t1);
      x2 = egraph_base_thvar(egraph, t2);

      if (x1 != null_thvar && x2 != null_thvar) {
	switch (egraph_type(egraph, t1)) {
	case ETYPE_INT:
	case ETYPE_REAL:
	  satellite = egraph->th[ETYPE_REAL];
	  interface = egraph->eg[ETYPE_REAL];
	  break;

	case ETYPE_BV:
	  satellite = egraph->th[ETYPE_BV];
	  interface = egraph->eg[ETYPE_BV];
	  break;

	default:
	  continue;
	}
      }

      if (interface->equal_in_model(satellite, x1, x2)) {
	/*
	 * Generate the interface lemma: (not (eq t1 t2)) => distinct x1 x2 in the theory
	 */
	eq = egraph_make_simple_eq(egraph, t1, t2);
	interface->gen_interface_lemma(satellite, not(eq), x1, x2, true);
	return 1;
      }
    }
  }

  return 0;
}



/*
 * Collect composite terms of the form (apply f ....) that are congruence
 * roots and where f is in class c
 * - all these are added to vector v
 */
static void egraph_collect_applications_in_class(egraph_t *egraph, class_t c, pvector_t *v) {
  use_vector_t *u;
  composite_t *p;
  occ_t f;
  uint32_t i, n;

  u = egraph_class_parents(egraph, c);
  n = u->last;
  for (i=0; i<n; i++) {
    p = u->data[i];
    if (valid_entry(p) && composite_kind(p) == COMPOSITE_APPLY) {
      f = composite_child(p, 0); // function term in p
      if (egraph_class(egraph, f) == c) {
	pvector_push(v, p);
      }
    }
  }
}



/*
 * Scan vector v of composites
 * - generate indirect interface lemmas based on its elements
 * - stop as soon as max_eqs is reached
 * - return the number of interface lemmas generated
 */
static uint32_t egraph_interface_lemmas_for_class(egraph_t *egraph, pvector_t *v, uint32_t max_eqs) {
  composite_t *cmp1, *cmp2;
  uint32_t i, j, n, neqs;

  neqs = 0;

  n = v->size;
  for (i=0; i<n; i++) {
    cmp1 = v->data[i];
    for (j=i+1; j<n; j++) {
      cmp2 = v->data[j];
      if (non_mergeable_in_models(egraph, cmp1->id, cmp2->id)) {
	neqs += check_interface_lemma_for_applies(egraph, cmp1, cmp2);
	if (neqs >= max_eqs) break;
      }
    }
  }

  return neqs;
}


/*
 * Check whether type tau is relevant for interface lemmas
 * - tau must have a function type [tau_1 ... tau_n -> sigma]
 * - one of tau_i must be an interprted type (int, real, bitvector, or another function type).
 */
static bool type_has_theory_domain(type_table_t *types, type_t tau) {
  function_type_t *d;
  uint32_t i, n;

  d = function_type_desc(types, tau);
  n = d->ndom;
  for (i=0; i<n; i++) {
    switch (type_kind(types, d->domain[i])) {
    case REAL_TYPE:
    case INT_TYPE:
    case BITVECTOR_TYPE:
      return true;

    default:
      break;
    }
  }

  return false;
}


#if 0

/*
 * Collect all function classes that may be relevant for indirect
 * interface lemmas.
 */
static void egraph_collect_relevant_classes(egraph_t *egraph, ivector_t *v) {
  uint32_t i, n;
  occ_t root;
  type_t tau;

  n = egraph_num_classes(egraph);
  for (i=0; i<n; i++) {
    if (egraph_class_type(egraph, i) == ETYPE_FUNCTION) {
      root = egraph_class_root(egraph, i);
      if (egraph_class(egraph, root) == i) {
	tau = egraph_term_real_type(egraph, term_of_occ(root));
	if (type_has_theory_domain(egraph->types, tau)) {
	  // i is root class and has a relevant type: add it to v
	  ivector_push(v, i);
	}
      }
    }
  }
}

#endif

/*
 * Generate indirect conflict lemmas
 * - stop as soon as max_eqs is reachecd
 * - return the number of lemmas generated
 */
static uint32_t egraph_indirect_interface_lemmas(egraph_t *egraph, uint32_t max_eqs) {
  pvector_t *v;
  uint32_t i, n;
  occ_t root;
  type_t tau;
  uint32_t neqs;
  

  neqs = 0;
  v = &egraph->cmp_vector;

  n = egraph_num_classes(egraph);
  for (i=0; i<n; i++) {
    if (egraph_class_type(egraph, i) == ETYPE_FUNCTION) {
      root = egraph_class_root(egraph, i);
      if (egraph_class(egraph, root) == i) {
	tau = egraph_term_real_type(egraph, term_of_occ(root));
	if (type_has_theory_domain(egraph->types, tau)) {
	  // i is root class and has a relevant type
	  pvector_reset(v);
	  egraph_collect_applications_in_class(egraph, i, v);
	  neqs += egraph_interface_lemmas_for_class(egraph, v, max_eqs - neqs);
	  if (neqs >= max_eqs) goto done;
	}
      }
    }
  }

 done:
  return neqs;
}



/****************************************************************************
 *  EXPERIMENTAL: MODIFY EGRAPH TO MINIMIZE THE NUMBER OF INTERFACE LEMMAS  *
 ***************************************************************************/

/*
 * Test: check whether there are duplicates in vector v
 */
static void check_interface_duplicates(ivector_t *v) {
  uint32_t i, j, n;
  occ_t t1, t2;

  n = v->size;
  for (i=0; i<n; i += 2) {
    t1 = v->data[i];
    t2 = v->data[i+1];
    for (j=i+2; j<n; j += 2) {
      if ((v->data[j] == t1 && v->data[j+1] == t2) 
	  || (v->data[j] == t2 && v->data[j+1] == t1)) {
	printf("---> EGRAPH: interface lemma duplicate: "
	       "v[%"PRIu32", %"PRIu32"] = (%"PRId32", %"PRId32"); "
	       "v[%"PRIu32", %"PRIu32"] = (%"PRId32", %"PRId32")\n", i, i+1, t1, t2, j, j+1, v->data[j], v->data[j+1]);
	fflush(stdout);
      }
    }
  }
}


/*
 * Generate interface lemmas for pairs of term occurrences stored in v
 * - stop as soon as max_eqs interface lemmas are produced
 * - return the number of lemmas generated
 */
static uint32_t egraph_gen_interface_lemmas(egraph_t *egraph, uint32_t max_eqs, ivector_t *v) {
  void *satellite;
  th_egraph_interface_t *interface;
  uint32_t i, n;
  occ_t t1, t2;
  thvar_t x1, x2;
  literal_t eq;

  check_interface_duplicates(v);

  n = v->size;
  assert(n > 0);
  if (n > 2 * max_eqs) {
    n = 2 * max_eqs;
  }

  for (i=0; i<n; i += 2) {
    t1 = v->data[i];
    t2 = v->data[i+1];
    assert(egraph_class(egraph, t1) != egraph_class(egraph, t2));
    x1 = egraph_base_thvar(egraph, t1);
    x2 = egraph_base_thvar(egraph, t2);
    assert(x1 != null_thvar && x2 != null_thvar);

    switch (egraph_type(egraph, t1)) {
    case ETYPE_INT:
    case ETYPE_REAL:
      satellite = egraph->th[ETYPE_REAL];
      interface = egraph->eg[ETYPE_REAL];
      break;

    case ETYPE_BV:
      satellite = egraph->th[ETYPE_BV];
      interface = egraph->eg[ETYPE_BV];
      break;
      
    default:
      assert(false);
      abort();
      break;
    }

    assert(interface->equal_in_model(satellite, x1, x2));
    eq = egraph_make_simple_eq(egraph, t1, t2);
    interface->gen_interface_lemma(satellite, not(eq), x1, x2, true);
  }

  assert(n/2 <= max_eqs);

  return n/2;
}


/*
 * Check whether x1 and x2 have different values in the relevant theory solver
 * - i = type of x1
 * - we ignore the function solver here
 */
static bool diseq_in_model(egraph_t *egraph, etype_t i, thvar_t x1, thvar_t x2) {
  switch (i) {
  case ETYPE_INT:
  case ETYPE_REAL:
  case ETYPE_BV:
    return !egraph->eg[i]->equal_in_model(egraph->th[i], x1, x2);

  default:
    return false;
  }
}

/*
 * Check whether the classes of t1 and t2 can be merged
 * - c1 must be the class of t1 and c2 must be the class of t2
 * - if c1 and c2 have theory variables, then they can be merged if the 
 *   variables have equal values in the theory model
 */
static bool mergeable_classes(egraph_t *egraph, occ_t t1, occ_t t2, class_t c1, class_t c2) {
  uint32_t msk;
  composite_t *cmp;
  thvar_t x1, x2;

  if (egraph_opposite_occ(egraph, t1, t2)) {
    return false;
  }

  assert(c1 != c2);

  msk = egraph->classes.dmask[c1] & egraph->classes.dmask[c2];
  if (msk != 0) {
    return false;
  }

  cmp = congruence_table_find_eq(&egraph->ctable, t1, t2, egraph->terms.label);
  if (cmp != NULL && egraph_occ_is_false(egraph, pos_occ(cmp->id))) {
    return false;
  }

  x1 = egraph_class_thvar(egraph, c1);
  x2 = egraph_class_thvar(egraph, c2);
 
  if (x1 != null_thvar && x2 != null_thvar && 
      diseq_in_model(egraph, egraph_class_type(egraph, c1), x1, x2)) {
    return false;
  }

  return true;
}


/*
 * Propagate equality v1 == v2 during reconciliation
 */
static void reconcile_thvar(egraph_t *egraph, class_t c1, thvar_t v1, class_t c2, thvar_t v2) {
  etype_t i;

  assert(v1 != null_thvar && v2 != null_thvar &&
	 v1 == egraph_class_thvar(egraph, c1) &&
	 v2 == egraph_class_thvar(egraph, c2));

  i = egraph->classes.etype[c1];

  switch (i) {
  case ETYPE_INT:
  case ETYPE_REAL:
  case ETYPE_BV:
    assert(egraph->eg[i]->equal_in_model(egraph->th[i], v1, v2));
    break;

  case ETYPE_FUNCTION:
    egraph->eg[i]->assert_equality(egraph->th[i], v1, v2);
    break;

  case ETYPE_BOOL:
    // all Boolean variables are already assigned in the core.
    break;

  case ETYPE_TUPLE:
    propagate_tuple_equality(egraph, v1, v2);
    break;

  default:
    assert(false);
  }
}


/*
 * Attempt to merge the classes of t1 and t2 without affecting the theory models
 * - t1 and t2 must not be Boolean
 * - i = correspondign edge id
 * - return true if t1 and t2 can be merged
 * - return false otherwise
 */
static bool test_merge(egraph_t *egraph, occ_t t1, occ_t t2, int32_t i) {
  use_vector_t *v;
  composite_t *p;
  class_t c1, c2;
  int32_t aux;
  uint32_t j, n;
  elabel_t l;
  occ_t t;
  thvar_t v1, v2;

  if (egraph_equal_occ(egraph, t1, t2)) {
    return true;
  }

  c1 = egraph_class(egraph, t1);
  c2 = egraph_class(egraph, t2);

  if (! mergeable_classes(egraph, t1, t2, c1, c2)) {
    return false;
  }

  assert(c1 != c2 && (egraph->classes.dmask[c1] & egraph->classes.dmask[c2]) == 0);

  // make sure c2 is the class with smallesrt parent vector
  if (egraph_class_nparents(egraph, c2) > egraph_class_nparents(egraph, c1)) {
    aux = t1; t1 = t2; t2 = aux;
    aux = c1; c1 = c2; c2 = aux;
  }

  // save t2 and its label for backtracking
  undo_stack_push_merge(&egraph->undo, t2, egraph_label(egraph, t2));
  
  // update the explanation tree
  invert_branch(egraph, t2);
  assert(egraph->terms.edge[term_of_occ(t2)] == null_edge);
  egraph->terms.edge[term_of_occ(t2)] = i; 

  // remove c2's parents from the congruence table
  v = egraph->classes.parents + c2;
  n = v->last;
  for (j=0; j<n; j++) {
    p  = v->data[j];
    if (valid_entry(p)) {
      // p is in the congruence table
      congruence_table_remove(&egraph->ctable, p);
      // remove p from the parent vectors (except v)
      separate_composite(p, egraph->terms.label, egraph->classes.parents, c2);
      assert(v->data[j] == p);
    }
  }

  // assign a new label to all terms in t2's class
  l = egraph_label(egraph, t1);
  t = t2;
  do {
    egraph_set_label(egraph, t, l);
    t = egraph_next(egraph, t);
    assert(term_of_occ(t) != term_of_occ(t2) || t == t2);
  } while (t != t2);

  // update dmask of c1
  egraph->classes.dmask[c1] |= egraph->classes.dmask[c2];

  //  merge lists of terms: swap next[t1] and next[t2]
  t = egraph_next(egraph, t2);
  egraph_set_next(egraph, t2, egraph_next(egraph, t1));
  egraph_set_next(egraph, t1, t);

  // reprocess all the composites in v 
  for (j=0; j<n; j++) {
    p = v->data[j];
    if (valid_entry(p)) {
      if (composite_simplifies(egraph, p)) {
	// p no longer a congruence root: put a mark for backtracking
	mark_use_vector_entry(v, j);
      } else {
	// put p back into the use vectors: this add p to c's parent
	attach_composite(p, egraph->terms.label, egraph->classes.parents);
      }
    }
  }

  /*
   * deal with the theory variables of c1 and c2: 
   */
  v2 = egraph->classes.thvar[c2];
  v1 = egraph->classes.thvar[c1];
  if (v1 != null_thvar) {
    assert(v2 != null_thvar);
    reconcile_thvar(egraph, c1, v1, c2, v2);
  }

  return true;
}



/*
 * Backtrack if a reconciliation attempt fails:
 * - k = top of the undo queue when the EXPL_RECONCILE edge was added
 *   (so this revert all merges in undo[k ... top-1]
 */
static void egraph_undo_reconcile_attempt(egraph_t *egraph, uint32_t k) {
  uint32_t i;
  unsigned char *utag;
  undo_t *udata;

  assert(k <= egraph->undo.top);

  i = egraph->undo.top;
  utag = egraph->undo.tag;
  udata = egraph->undo.data;

  while (i > k) {
    i --;
    switch (utag[i]) {
    case UNDO_MERGE:
      undo_merge(egraph, udata[i].merge.saved_occ, udata[i].merge.saved_label);
      break;

    case UNDO_SIMPLIFY:
      restore_composite(egraph, udata[i].ptr);
      break;

    case UNDO_DISTINCT:
      assert(false); // should not happen
      undo_distinct(egraph);
      break;
      
    // store terms to reanalyze into reanalyze_vector
    case REANALYZE_CONGRUENCE_ROOT:
      deactivate_congruence_root(egraph, udata[i].ptr);
      pvector_push(&egraph->reanalyze_vector, udata[i].ptr);
      break;

    case REANALYZE_COMPOSITE:
      pvector_push(&egraph->reanalyze_vector, udata[i].ptr);
      break;

    default:
      assert(false);
      break;
    }
  }

  assert(i == k);
  egraph->undo.top = k;
}



/*
 * Collect an interface equality (t1 == t2) when reconciliation fails
 * - i = conflict egde
 */
static void collect_interface_pair(egraph_t *egraph, int32_t i) {
  equeue_elem_t *e;
  ivector_t *v;
  int32_t k;

  k = egraph_get_reconcile_edge(egraph, i);
  e = egraph->stack.eq + k;

  v = &egraph->interface_eqs;
  ivector_push(v, e->lhs);
  ivector_push(v, e->rhs);
}


/*
 * Propagate equalities during reconciliation
 */
static bool egraph_prop_reconcile(egraph_t *egraph) {
  equeue_elem_t *e;
  uint32_t i;

  i = egraph->stack.prop_ptr;
  while (i < egraph->stack.top) {
    e = egraph->stack.eq + i;
    if (!test_merge(egraph, e->lhs, e->rhs, i)) {
      collect_interface_pair(egraph, i);
      return false;
    }
    i ++;
  }
  egraph->stack.prop_ptr = i;

  return true;
}


/*
 * Attempt to make t1 and t2 equal in the egraph then propagate
 * - return false if that leads to a conflict
 * - return true otherwise
 */
static bool egraph_reconcile_pair(egraph_t *egraph, occ_t t1, occ_t t2) {
  int32_t k;
  uint32_t top;

  assert(egraph->stack.prop_ptr == egraph->stack.top);

  if (egraph_equal_occ(egraph, t1, t2)) {
    return true;  // already equal: nothing to do
  }

  top = egraph->undo.top;
  k = egraph_stack_push_eq(&egraph->stack, t1, t2);
  assert(k == egraph->stack.prop_ptr);

  egraph->stack.etag[k] = EXPL_RECONCILE;
  if (egraph_prop_reconcile(egraph)) {
    return true;
  }

  // clean up
  egraph_undo_reconcile_attempt(egraph, top);
  egraph->stack.top = k;
  egraph->stack.prop_ptr = k;
  return false;
}


/*
 * Process a class of terms
 * - every element of v is a variable in a theory solver
 * - solver = the theory solver for v
 * - eg= the egraph interface for that solver
 */
static bool egraph_reconcile_class(egraph_t *egraph, int32_t *v, void *solver, th_egraph_interface_t *eg) {
  uint32_t i, n;
  eterm_t t1, t2;

  n = iv_size(v);
  assert(n >= 2);

  t1 = eg->eterm_of_var(solver, v[0]);
  for (i=1; i<n; i++) {
    t2 = eg->eterm_of_var(solver, v[i]);
    if (!egraph_reconcile_pair(egraph, pos_occ(t1), pos_occ(t2))) {
      return false;
    }
  }

  return true;
}



/*
 * Process a term partition
 * - return true if all terms of every class in part can be reconciled
 * - return false otherwise
 */
static bool egraph_reconcile_partition(egraph_t *egraph, ipart_t *partition, void *solver, th_egraph_interface_t *eg) {
  int32_t *v;
  uint32_t i, n;
  bool reconciled;

  reconciled = true;
  n = int_partition_nclasses(partition);
  for (i=0; i<n; i++) {
    v = partition->classes[i];
    reconciled &= egraph_reconcile_class(egraph, v, solver, eg);
  }

  return reconciled;
}



/*
 * Try model reconciliation: return true if that worked, false otherwise
 * - if the result is false then candidates for interface lemmas are
 *   stored in egraph->interface_eqs.
 */
static bool egraph_reconcile(egraph_t *egraph) {
  ipart_t *partition;
  bool reconciled;

  reconciled = true;

  if (egraph->ctrl[ETYPE_REAL] != NULL) {
    partition = egraph->eg[ETYPE_REAL]->build_model_partition(egraph->th[ETYPE_REAL]);
    reconciled = egraph_reconcile_partition(egraph, partition, egraph->th[ETYPE_REAL], egraph->eg[ETYPE_REAL]);
    egraph->eg[ETYPE_REAL]->release_model_partition(egraph->th[ETYPE_REAL], partition);
  }

  if (egraph->ctrl[ETYPE_BV] != NULL) {
    partition = egraph->eg[ETYPE_BV]->build_model_partition(egraph->th[ETYPE_BV]);
    reconciled &= egraph_reconcile_partition(egraph, partition, egraph->th[ETYPE_BV], egraph->eg[ETYPE_BV]);
    egraph->eg[ETYPE_BV]->release_model_partition(egraph->th[ETYPE_BV], partition);
  }

  return reconciled;
}



// HACK: use global variables for testing
static uint32_t reco_undo_top;
static uint32_t reco_num_eqs;

/*
 * Prepare for reconciliation:
 * - store the current number of equalities + the top of the undo stack
 */
static void egraph_start_reconciliation(egraph_t *egraph) {
  assert(egraph->stack.prop_ptr == egraph->stack.top);

  reco_undo_top = egraph->undo.top;
  reco_num_eqs = egraph->stack.top;
}


/*
 * Restore the egraph state to what it was before reconciliation:
 */
static void egraph_reconciliation_restore(egraph_t *egraph) {
  egraph_undo_reconcile_attempt(egraph, reco_undo_top);
  egraph->stack.top = reco_num_eqs;
  egraph->stack.prop_ptr = reco_num_eqs;
}





/*****************
 *  FINAL CHECK  *
 ****************/

/*
 * BASELINE VERSION OF FINAL CHECK
 * - call final_check on all satellites then use the reconcile_model
 *   funciton in each solver
 */
static fcheck_code_t baseline_final_check(egraph_t *egraph) {
  fcheck_code_t c;
  uint32_t i, max_eq;

  //  printf("---> EGRAPH: final check (baseline)\n");

  if (egraph->ctrl[ETYPE_REAL] != NULL) {
    // arithmetic solver
    c = egraph->ctrl[ETYPE_REAL]->final_check(egraph->th[ETYPE_REAL]);
    if (c != FCHECK_SAT) {
      //      printf("---> exit at arith final check\n");
      return c;
    }
  }

  if (egraph->ctrl[ETYPE_BV] != NULL) {
    // bitvector solver
    c = egraph->ctrl[ETYPE_BV]->final_check(egraph->th[ETYPE_BV]);
    if (c != FCHECK_SAT) {
      //      printf("---> exit at bv final check\n");
      return c;
    }
  }

  if (egraph->ctrl[ETYPE_FUNCTION] != NULL) {
    // array solver
    c = egraph->ctrl[ETYPE_FUNCTION]->final_check(egraph->th[ETYPE_FUNCTION]);
    if (c != FCHECK_SAT) {
      //      printf("---> exit at array final check\n");
      return c;
    }
  }


  // i = number of interface equalities generated
  // max_eq = bound on number of interface equalities
  max_eq = egraph->max_interface_eqs;
  i = 0;
  assert(i < max_eq);

  if (egraph->ctrl[ETYPE_REAL] != NULL) {
    // reconcile for arithmetic solver
    assert(egraph->eg[ETYPE_REAL] != NULL);
    i = egraph->eg[ETYPE_REAL]->reconcile_model(egraph->th[ETYPE_REAL], max_eq);      
  }

  if (i < max_eq && egraph->ctrl[ETYPE_BV] != NULL) {
    // reconcile in bitvector solver
    assert(egraph->eg[ETYPE_BV] != NULL);
    i += egraph->eg[ETYPE_BV]->reconcile_model(egraph->th[ETYPE_BV], max_eq - i);
  }

  if (i > 0) {
    //    printf("---> %"PRIu32" interface lemmas from bv/arith solvers\n", i);
  }
    
  if (i == 0 && egraph->ctrl[ETYPE_FUNCTION] != NULL && egraph_is_high_order(egraph)) {
    /*
     * reconcile for array solver: do it only if bv and arith models
     * are consistent with the egraph. Also there's nothing to do
     * if there are no high-order terms.
     */
    assert(egraph->eg[ETYPE_FUNCTION] != NULL);
    i = egraph->eg[ETYPE_FUNCTION]->reconcile_model(egraph->th[ETYPE_FUNCTION], 1);
    if (i > 0) {
      //      printf("---> %"PRIu32" interface lemmas from array solver\n", i);
    }
  }

  egraph->stats.interface_eqs += i;
  
  c = FCHECK_SAT; // default value
  if (i > 0) {
    c = FCHECK_CONTINUE;
  }

  return c;   
}


/*
 * New: experimental version
 */
static fcheck_code_t experimental_final_check(egraph_t *egraph) {
  fcheck_code_t c;
  uint32_t i, max_eqs;

  //  printf("---> EGRAPH: final check (experimental)\n");

  if (egraph->ctrl[ETYPE_REAL] != NULL) {
    c = egraph->ctrl[ETYPE_REAL]->final_check(egraph->th[ETYPE_REAL]);
    if (c != FCHECK_SAT) {
      //      printf("---> exit at arith final check\n");
      return c;
    }
  }

  if (egraph->ctrl[ETYPE_BV] != NULL) {
    // bitvector solver
    c = egraph->ctrl[ETYPE_BV]->final_check(egraph->th[ETYPE_BV]);
    if (c != FCHECK_SAT) {
      //      printf("---> exit at bv final check\n");
      return c;
    }
  }


  /*
   * Try egraph reconciliation
   */
  c = FCHECK_SAT;
  egraph_prepare_models(egraph);
  egraph_start_reconciliation(egraph);

  if (! egraph_reconcile(egraph)) {
    egraph_reconciliation_restore(egraph);
    
    // Generate interface equalities
    max_eqs = egraph->max_interface_eqs;
    i = egraph_gen_interface_lemmas(egraph, max_eqs, &egraph->interface_eqs);
    egraph->stats.interface_eqs += i;
    ivector_reset(&egraph->interface_eqs);
    c = FCHECK_CONTINUE;

    //    printf("---> egraph reconcile failed: %"PRIu32" interface lemmas\n", i);

  } else if (egraph->ctrl[ETYPE_FUNCTION] != NULL) {
    /*
     * bv/arith models are consistent with the egraph:
     * deal with the array solver
     */
    c = egraph->ctrl[ETYPE_FUNCTION]->final_check(egraph->th[ETYPE_FUNCTION]);    
    if (c == FCHECK_SAT) {
      if (egraph_is_high_order(egraph)) {
	i = egraph->eg[ETYPE_FUNCTION]->reconcile_model(egraph->th[ETYPE_FUNCTION], 1);
	if (i > 0) {
	  //	  printf("---> exit after array reconcile: %"PRIu32" lemmas\n", i);
	  c = FCHECK_CONTINUE;
	}
      }
    } else {
      //      printf("---> exit at array final check\n");
    }

    if (c != FCHECK_SAT) {
      egraph_reconciliation_restore(egraph);
    }
  }
  
  egraph_release_models(egraph);

  return c;
}


/*
 * Call final check for all the satellite solvers
 * If all return SAT, try to build consistent models
 * If models are not consistent, generate interface equalities
 */
fcheck_code_t egraph_final_check(egraph_t *egraph) {
  egraph->stats.final_checks ++;

  if (true) {
    return baseline_final_check(egraph);
  } else {
    return experimental_final_check(egraph);
  }
}





/****************
 *  ASSERTIONS  *
 ***************/

/*
 * Assert (t == true) with explanation l
 * - term_of_occ(t) must be a boolean term
 */
void egraph_assert_term(egraph_t *egraph, occ_t t, literal_t l) {
  int32_t k;

#if TRACE
  printf("---> EGRAPH: Asserting term ");
  print_occurrence(stdout, t);
  printf(", expl = ");
  print_literal(stdout, l);
  printf(", decision level = %"PRIu32"\n", egraph->decision_level);
  if (egraph_term_is_composite(egraph, term_of_occ(t))) {
    printf("---> ");
    print_eterm_def(stdout, egraph, term_of_occ(t));
  }
  if (egraph_occ_is_true(egraph, t)) {
    printf("---> EGRAPH: Term ");
    print_occurrence(stdout, t);
    printf(" is already true\n");
  }
#endif

  // don't do anything if t is already true
  if (! egraph_occ_is_true(egraph, t)) {
    k = egraph_stack_push_eq(&egraph->stack, t, true_occ);
    egraph->stack.etag[k] = EXPL_ASSERT;
    egraph->stack.edata[k].lit = l;
  }
}

/*
 * Assert (t1 == t2) with explanation l
 */
void egraph_assert_eq(egraph_t *egraph, occ_t t1, occ_t t2, literal_t l) {
  int32_t k;

#if TRACE
  printf("---> EGRAPH: Asserting ");
  print_occurrence(stdout, t1);
  printf(" == ");
  print_occurrence(stdout, t2);
  printf(" , expl = ");
  print_literal(stdout, l);
  printf(", decision level = %"PRIu32"\n", egraph->decision_level);
  if (egraph_equal_occ(egraph, t1, t2)) {
    printf("---> EGRAPH: ");
    print_occurrence(stdout, t1);
    printf(" and ");
    print_occurrence(stdout, t2);
    printf(" are already equal\n");
  }
#endif

  // don't do anything if t1 and t2 are already equal
  if (! egraph_equal_occ(egraph, t1, t2)) {
    k = egraph_stack_push_eq(&egraph->stack, t1, t2);
    egraph->stack.etag[k] = EXPL_ASSERT;
    egraph->stack.edata[k].lit = l;
  }
}



/*
 * Assert atom atm with explanation l (propagation from the core)
 * - if l has positive polarity then atom is asserted true
 *   if l has negative polarity then atom is asserted false
 * - forward to arithmetic or bitvector solver if required
 * - return false if there's a conflict, true otherwise
 */
bool egraph_assert_atom(egraph_t *egraph, void *atom, literal_t l) {
  atom_t *a;
  occ_t t;
  bool resu;

  resu = true;

  switch (atom_tag(atom)) {
  case EGRAPH_ATM_TAG:
    a = (atom_t *) untag_atom(atom);
    assert(a->boolvar == var_of(l));
    t = mk_occ(a->eterm, sign_of(l));
    egraph_assert_term(egraph, t, l);
    break;

  case ARITH_ATM_TAG:
    resu = egraph->arith_smt->assert_atom(egraph->th[ETYPE_INT], untag_atom(atom), l);
    break;

  case BV_ATM_TAG:
    resu = egraph->bv_smt->assert_atom(egraph->th[ETYPE_BV], untag_atom(atom), l);
    break;
  }

  return resu;
}


/*
 * Assert (t == true) as an axiom
 * - axiom assertion is allowed at the base level only
 */
void egraph_assert_axiom(egraph_t *egraph, occ_t t) {
  int32_t k;

#if TRACE
  printf("---> EGRAPH: Asserting axiom ");
  print_occurrence(stdout, t);
  printf(", decision level = %"PRIu32"\n", egraph->decision_level);
  if (egraph_term_is_composite(egraph, term_of_occ(t))) {
    printf("---> ");
    print_eterm_def(stdout, egraph, term_of_occ(t));
  }
#endif

  assert(egraph->decision_level == egraph->base_level);
  k = egraph_stack_push_eq(&egraph->stack, true_occ, t);
  egraph->stack.etag[k] = EXPL_AXIOM;
}


/*
 * Assert (t1 == t2) as an axiom
 */
void egraph_assert_eq_axiom(egraph_t *egraph, occ_t t1, occ_t t2) {
  int32_t k;

#if TRACE
  printf("---> EGRAPH: Asserting axiom ");
  print_occurrence(stdout, t1);
  printf(" == ");
  print_occurrence(stdout, t2);
  printf(", decision level = %"PRIu32"\n", egraph->decision_level);
#endif

  assert(egraph->decision_level == egraph->base_level);
  k = egraph_stack_push_eq(&egraph->stack, t1, t2);
  egraph->stack.etag[k] = EXPL_AXIOM;
}


/*
 * Assert (t1 != t2) as an axiom
 * - create equality atom l --> (eq t1 t2) then assert not(l) 
 *   in the core
 */
void egraph_assert_diseq_axiom(egraph_t *egraph, occ_t t1, occ_t t2) {
#if CONSERVATIVE_DISEQ_AXIOMS
  literal_t l;
#else 
  occ_t eq;
  int32_t k;
#endif


#if TRACE
  printf("---> EGRAPH: Asserting axiom ");
  print_occurrence(stdout, t1);
  printf(" != ");
  print_occurrence(stdout, t2);
  printf(", decision level = %"PRIu32"\n", egraph->decision_level);
#endif

  assert(egraph->decision_level == egraph->base_level);
#if CONSERVATIVE_DISEQ_AXIOMS
  // conservative approach
  l = egraph_make_eq(egraph, t1, t2);
  add_unit_clause(egraph->core, not(l));
#else
  // avoid creation of an atom: eq has no theory variable attached
  eq = egraph_make_eq_term(egraph, t1, t2);
  k = egraph_stack_push_eq(&egraph->stack, eq, false_occ);
  egraph->stack.etag[k] = EXPL_AXIOM;
#endif  
}


/*
 * Assert (distinct t1 ... tn) as an axiom
 */
void egraph_assert_distinct_axiom(egraph_t *egraph, uint32_t n, occ_t *t) {
  eterm_t d;
  int32_t k;
  uint32_t i, j;

  assert(egraph->decision_level == egraph->base_level);
  d = egraph_distinct_term(egraph, n, t);
  if (d != null_eterm) {
    if (egraph_term_is_fresh(egraph, d)) {
      egraph_set_term_real_type(egraph, d, bool_type(egraph->types));
      egraph_activate_term(egraph, d, ETYPE_BOOL, const_bvar);
    }
#if TRACE
    printf("---> EGRAPH: Asserting axiom ");
    print_composite(stdout, egraph->terms.body[d]);
    printf(", decision level = %"PRIu32"\n", egraph->decision_level);
#endif
    k = egraph_stack_push_eq(&egraph->stack, pos_occ(d), true_occ);
    egraph->stack.etag[k] = EXPL_AXIOM;

  } else {
    /*
     * Too many distinct terms. Expand into n*(n-1)/2 disequalities
     */
    for (i=0; i<n-1; i++) {
      for (j=i+1; j<n; j++) {
	egraph_assert_diseq_axiom(egraph, t[i], t[j]);
      }
    }
  }
}


/*
 * Assert not (distinct t_1 ... t_n) as an axiom:
 * this adds the clause "(eq t_1 t_2) or .... or (eq t_n-1 t_n)" to the core
 */
void egraph_assert_notdistinct_axiom(egraph_t *egraph, uint32_t n, occ_t *t) {
  ivector_t *v;

  assert(egraph->decision_level == egraph->base_level);
  v = &egraph->aux_buffer;
  expand_distinct(egraph, n, t, v);
  add_clause(egraph->core, v->size, v->data);
}


/*
 * Assert (f a_1 ... a_n) as an axiom
 * - build term t := (f a_1 ... a_n) and add const_bvar as its theory variable
 * - push equality (t == true)
 */
void egraph_assert_pred_axiom(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a) {
  eterm_t t;
  int32_t k;

  t = egraph_apply_term(egraph, f, n, a);
  if (egraph_term_is_fresh(egraph, t)) {
    /*
     * HACK: we attach bool_const as theory variable of t
     * but we attach no theory variable to the class of t
     * (thvar[t] is used by the ackermann lemma function)
     */
    egraph_set_term_real_type(egraph, t, bool_type(egraph->types));
    egraph_activate_term(egraph, t, ETYPE_BOOL, null_thvar);
    egraph->terms.thvar[t] = const_bvar;

  } else if (egraph->terms.thvar[t] == null_thvar) {
    egraph->terms.thvar[t] = const_bvar;
  }

  k = egraph_stack_push_eq(&egraph->stack, true_occ, pos_occ(t));
  egraph->stack.etag[k] = EXPL_AXIOM;
}


/*
 * Assert not (f t_1 ... t_n) as an axiom:
 * build literal l = (f t_1 ... t_n) then assert not l in the core
 */
void egraph_assert_notpred_axiom(egraph_t *egraph, occ_t f, uint32_t n, occ_t *t) {
  literal_t l;

  l = egraph_make_pred(egraph, f, n, t);
  add_unit_clause(egraph->core, not(l));
}




/******************************************
 *  EQUALITY PROPAGATION FROM SATELLITES  *
 *****************************************/

/*
 * Propagation from a satellite solver
 * - add the equality (t1 == t2) to the propagation queue with explanation expl
 * - id = code to identify the satellite solver
 *   valid codes are EXPL_ARITH_PROPAGATION, EXPL_BV_PROPAGATION, EXPL_FUN_PROPAGATION
 * - expl = whatever the solver needs to explain the equality
 */
void egraph_propagate_equality(egraph_t *egraph, eterm_t t1, eterm_t t2, expl_tag_t id, void *expl) {
  int32_t k;

  assert((id == EXPL_ARITH_PROPAGATION && egraph_term_is_arith(egraph, t1) && 
	  egraph_term_is_arith(egraph, t2)) ||
	 (id == EXPL_BV_PROPAGATION && egraph_term_is_bv(egraph, t1) && egraph_term_is_bv(egraph, t2)) ||
	 (id == EXPL_FUN_PROPAGATION && egraph_term_is_function(egraph, t1) && 
	  egraph_term_is_function(egraph, t2)));

  if (egraph_equal_occ(egraph, pos_occ(t1), pos_occ(t2))) { 
    // redundant
    return;
  }

  k = egraph_stack_push_eq(&egraph->stack, pos_occ(t1), pos_occ(t2));
  egraph->stack.etag[k] = id;
  egraph->stack.edata[k].ptr = expl;
}



/************************
 *  THEORY EXPLANATION  *
 ***********************/

/*
 * Expand a theory implication:
 * - a theory solver called propagate_literal(core, l, expl)
 * - the core needs to convert expl to a conjunction of literals
 */
void egraph_expand_explanation(egraph_t *egraph, literal_t l, void *expl, ivector_t *v) {
  void *atom;
  atom_t *a;
  occ_t u;

  assert(v->size == 0);

  atom = get_bvar_atom(egraph->core, var_of(l));
  switch (atom_tag(atom)) {
  case EGRAPH_ATM_TAG:
    a = (atom_t *) atom;
    assert(a->boolvar == var_of(l));
    assert(bvar_value(egraph->core, var_of(l)) == egraph_term_truth_value(egraph, a->eterm));
    u = mk_occ(a->eterm, sign_of(l));
    /*
     * Build the explantion for u == true
     */
    egraph_explain_equality(egraph, u, true_occ, v);
    break;

  case ARITH_ATM_TAG:
    egraph->arith_smt->expand_explanation(egraph->th[ETYPE_INT], l, expl, v);
    break;

  case BV_ATM_TAG:
    egraph->bv_smt->expand_explanation(egraph->th[ETYPE_BV], l, expl, v);
    break;
  }
}




/*************************
 *  SPLITTING HEURISTIC  *
 ************************/

/*
 * For an equality atom c = (eq t1 t2) and l attached to that atom
 * select whether to branch on l or (not l)
 * - if t1 and t2 are attached to theory variables, the decision is 
 *   made by the satellite solver
 * - otherwise, return l
 */
static literal_t egraph_select_eq_polarity(egraph_t *egraph, composite_t *c, literal_t l) {
  occ_t t1, t2;
  class_t c1, c2;
  thvar_t v1, v2;
  etype_t i;

  assert(composite_kind(c) == COMPOSITE_EQ);

  t1 = c->child[0];
  t2 = c->child[1];
  i = egraph_type(egraph, t1);
  if (i < NUM_SATELLITES) {
    c1 = egraph_class(egraph, t1);
    v1 = egraph->classes.thvar[c1];
    c2 = egraph_class(egraph, t2);
    v2 = egraph->classes.thvar[c2];
    if (v1 != null_thvar && v2 != null_thvar) {
      assert(egraph->eg[i] != NULL);
      return egraph->eg[i]->select_eq_polarity(egraph->th[i], v1, v2, pos_lit(var_of(l)));
    }
  }

  return l;
}


/*
 * Select whether to branch on l or (not l)
 * - atom = the atom attached to var_of(l)
 * - forward to the appropriate subsolver 
 */
static literal_t egraph_select_polarity(egraph_t *egraph, void *atom, literal_t l) {
  atom_t *a;
  composite_t *c;

  switch (atom_tag(atom)) {
  case ARITH_ATM_TAG:
    return egraph->arith_smt->select_polarity(egraph->th[ETYPE_INT], untag_atom(atom), l);

  case BV_ATM_TAG:
    return egraph->bv_smt->select_polarity(egraph->th[ETYPE_BV], untag_atom(atom), l);

  case EGRAPH_ATM_TAG:
  default:
    // FOR EQUALITY ATOMS: defer to the satellite solver if any
    a = (atom_t *) untag_atom(atom);
    assert(a->boolvar == var_of(l));
    c = egraph_term_body(egraph, a->eterm);
    if (composite_body(c) && composite_kind(c) == COMPOSITE_EQ) {
      l = egraph_select_eq_polarity(egraph, c, l);
    }
    return l;
  }
}







/***********************
 *  CONTROL INTERFACE  *
 **********************/

static th_ctrl_interface_t egraph_control = {
  (start_intern_fun_t) egraph_start_internalization,
  (start_fun_t) egraph_start_search,
  (propagate_fun_t) egraph_propagate,
  (final_check_fun_t) egraph_final_check,
  (increase_level_fun_t) egraph_increase_decision_level,
  (backtrack_fun_t) egraph_backtrack,
  (push_fun_t) egraph_push,
  (pop_fun_t) egraph_pop,
  (reset_fun_t) egraph_reset,
};



/*******************
 *  SMT INTERFACE  *
 ******************/

static th_smt_interface_t egraph_smt = {
  (assert_fun_t) egraph_assert_atom,
  (expand_expl_fun_t) egraph_expand_explanation,
  (select_pol_fun_t) egraph_select_polarity,
  NULL,
  NULL,
};




/*************************
 *  EGRAPH CONSTRUCTION  *
 ************************/

/*
 * Initialize all internal structures
 * - ttbl = attached type table
 * - use default initial sizes
 * - subsolver descriptors are all NULL and core is also NULL
 * - set all options and parameters to their default values
 */
void init_egraph(egraph_t *egraph, type_table_t *ttbl) {
  uint32_t i;

  egraph->core = NULL;
  egraph->types = ttbl;

  egraph->base_level = 0;
  egraph->decision_level = 0;
  egraph->ndistincts = 0;
  egraph->is_high_order = false;

  init_egraph_stats(&egraph->stats);

  egraph->options = EGRAPH_DEFAULT_OPTIONS;
  egraph->max_ackermann = DEFAULT_MAX_ACKERMANN;
  egraph->max_boolackermann = DEFAULT_MAX_BOOLACKERMANN;
  egraph->aux_eq_quota = DEFAULT_AUX_EQ_QUOTA;
  egraph->ackermann_threshold = DEFAULT_ACKERMANN_THRESHOLD;
  egraph->boolack_threshold = DEFAULT_BOOLACK_THRESHOLD;
  egraph->max_interface_eqs = DEFAULT_MAX_INTERFACE_EQS;
  egraph->ack_left = null_occurrence;
  egraph->ack_right = null_occurrence;

  init_class_table(&egraph->classes, DEFAULT_CLASS_TABLE_SIZE);
  init_eterm_table(&egraph->terms, DEFAULT_ETERM_TABLE_SIZE);
  init_egraph_stack(&egraph->stack, DEFAULT_EGRAPH_STACK_SIZE, DEFAULT_EGRAPH_NLEVELS);
  init_undo_stack(&egraph->undo, DEFAULT_EGRAPH_STACK_SIZE, DEFAULT_EGRAPH_NLEVELS);
  init_distinct_table(&egraph->dtable);
  init_congruence_table(&egraph->ctable, 0);

  init_egraph_trail(&egraph->trail_stack);


  // auxiliary buffers and data structures
  egraph->const_htbl = NULL;
  init_int_htbl(&egraph->htbl, 0);
  init_objstore(&egraph->atom_store, sizeof(atom_t), ATOM_BANK_SIZE); 
  init_cache(&egraph->cache);

  egraph->imap = NULL;
  init_sign_buffer(&egraph->sgn);
  init_arena(&egraph->arena);
  init_ivector(&egraph->expl_queue, DEFAULT_EXPL_VECTOR_SIZE);
  init_ivector(&egraph->expl_vector, DEFAULT_EXPL_VECTOR_SIZE);
  init_pvector(&egraph->cmp_vector, DEFAULT_CMP_VECTOR_SIZE);
  init_ivector(&egraph->aux_buffer, 0);
  init_ivector(&egraph->interface_eqs, 40);
  init_pvector(&egraph->reanalyze_vector, 0);
  init_th_explanation(&egraph->th_expl);
  egraph->app_partition = NULL;

  // satellite solvers and descriptors
  for (i=0; i<NUM_SATELLITES; i++) {
    egraph->th[i] = NULL;
    egraph->ctrl[i] = NULL;
    egraph->eg[i] = NULL;
  }
  egraph->arith_smt = NULL;
  egraph->bv_smt = NULL;
  egraph->arith_eg = NULL;
  egraph->bv_eg = NULL;
  egraph->fun_eg = NULL;

  // model-construction object
  init_egraph_model(&egraph->mdl);
}




/*
 * Attach an arithmetic solver: it's used for both INT and REAL
 * - the control interface is attached only to type REAL
 *   so that push/pop/reset/start_search are not called twice
 */
void egraph_attach_arithsolver(egraph_t *egraph, void *solver, th_ctrl_interface_t *ctrl,
			       th_smt_interface_t *smt, th_egraph_interface_t *eg,
			       arith_egraph_interface_t *arith_eg) {

  assert(egraph->core == NULL && egraph->arith_smt == NULL);

  egraph->th[ETYPE_INT] = solver;
  egraph->th[ETYPE_REAL] = solver;
  egraph->ctrl[ETYPE_INT] = NULL;
  egraph->ctrl[ETYPE_REAL] = ctrl;
  egraph->eg[ETYPE_INT] = eg;
  egraph->eg[ETYPE_REAL] = eg;
  egraph->arith_smt = smt;
  egraph->arith_eg = arith_eg;
}


/*
 * Attach a bitvector solver
 */
void egraph_attach_bvsolver(egraph_t *egraph, void *solver, th_ctrl_interface_t *ctrl,
			    th_smt_interface_t *smt, th_egraph_interface_t *eg,
			    bv_egraph_interface_t *bv_eg) {

  assert(egraph->core == NULL && egraph->bv_smt == NULL);

  egraph->th[ETYPE_BV] = solver;
  egraph->ctrl[ETYPE_BV] = ctrl;
  egraph->eg[ETYPE_BV] = eg;
  egraph->bv_smt = smt;
  egraph->bv_eg = bv_eg;
}


/*
 * Attach a function subsolver
 * - solver = pointer to the subsolver object
 * - ctrl, eg, fun_eg  = interface descriptors
 */
void egraph_attach_funsolver(egraph_t *egraph, void *solver, th_ctrl_interface_t *ctrl,
			     th_egraph_interface_t *eg, fun_egraph_interface_t *fun_eg) {
  etype_t id;

  assert(egraph->core == NULL && egraph->ctrl[ETYPE_FUNCTION] == NULL);

  id = ETYPE_FUNCTION;
  egraph->th[id] = solver;
  egraph->ctrl[id] = ctrl;
  egraph->eg[id] = eg;
  egraph->fun_eg = fun_eg;
}


/*
 * Get the egraph control and smt interfaces:
 */
th_ctrl_interface_t *egraph_ctrl_interface(egraph_t *egraph) {
  return &egraph_control;
}

th_smt_interface_t *egraph_smt_interface(egraph_t *egraph) {
  return &egraph_smt;
}


/*
 * Attach the core to the egraph
 * - the core must be initialized with the egraph_control and egraph_smt_interface
 */
void egraph_attach_core(egraph_t *egraph, smt_core_t *core) {
  assert(core != NULL && core->th_solver == egraph);

  egraph->core = core;
  egraph_init_constant(egraph);
}


/*
 * Delete everything
 */
void delete_egraph(egraph_t *egraph) {
  delete_egraph_model(&egraph->mdl);
  if (egraph->app_partition != NULL) {
    delete_ptr_partition(egraph->app_partition);
    safe_free(egraph->app_partition);
    egraph->app_partition = NULL;
  }
  delete_th_explanation(&egraph->th_expl);
  delete_pvector(&egraph->reanalyze_vector);
  delete_ivector(&egraph->interface_eqs);
  delete_ivector(&egraph->aux_buffer);
  delete_pvector(&egraph->cmp_vector);
  delete_ivector(&egraph->expl_vector);
  delete_ivector(&egraph->expl_queue);
  delete_arena(&egraph->arena);
  delete_sign_buffer(&egraph->sgn);
  if (egraph->imap != NULL) {
    delete_int_hmap(egraph->imap);
    safe_free(egraph->imap);
    egraph->imap = NULL;
  }
  delete_cache(&egraph->cache);
  delete_objstore(&egraph->atom_store);
  delete_int_htbl(&egraph->htbl);
  egraph_free_const_htbl(egraph);
  delete_egraph_trail(&egraph->trail_stack);
  delete_congruence_table(&egraph->ctable);  
  delete_undo_stack(&egraph->undo);
  delete_egraph_stack(&egraph->stack);
  delete_eterm_table(&egraph->terms);
  delete_class_table(&egraph->classes);
}




/*************************************
 *  SUPPORT FOR ARRAY-THEORY SOLVER  *
 ************************************/

/*
 * Collect all composite terms of the form (apply g ....)
 * where g is in the same class as f
 * - only the congruence roots are collected
 * - they are added to the pointer vector *v
 */
void egraph_collect_applications(egraph_t *egraph, eterm_t f, pvector_t *v) {
  use_vector_t *u;
  composite_t *p;
  class_t c;
  occ_t g;
  uint32_t i, n;

  c = egraph_term_class(egraph, f);
  u = egraph_class_parents(egraph, c);
  n = u->last;
  for (i=0; i<n; i++) {
    p = u->data[i];
    if (valid_entry(p) && composite_kind(p) == COMPOSITE_APPLY) {
      g = composite_child(p, 0); // function term of p
      if (egraph_class(egraph, g) == c) {
	pvector_push(v, p);
      }
    }
  }
}


/*
 * Return a term congruent to (apply g i_1 ... i_n) or NULL_COMPOSITE if there isn't one
 * - c = composite of the form (apply f i_1 ... i_n) 
 */
composite_t *egraph_find_modified_application(egraph_t *egraph, eterm_t g, composite_t *c) {
  signature_t *sgn;
  elabel_t *label;

  assert(composite_kind(c) == COMPOSITE_APPLY);

  label = egraph->terms.label;
  sgn = &egraph->sgn;
  signature_modified_apply(c, g, label, sgn);
  return congruence_table_find(&egraph->ctable, sgn, label);
}



/*
 * Return a randomly chosen class label of type tau
 * - if there's no term of type tau, return null_label
 */
elabel_t egraph_get_label_for_type(egraph_t *egraph, type_t tau) {
  uint32_t n, k;
  eterm_t t, u;


  if (is_boolean_type(tau)) {
    // select true or false randomly
    k = random_uint32();
    if (k & 0x400) {
      return true_label;
    } else {
      return false_label;
    }

  } else {

    n = egraph_num_terms(egraph);
    u = null_eterm;
    k = 0;
    for (t=0; t<n; t++) {
      if (egraph_term_real_type(egraph, t) == tau) {
	k ++;
	if (random_uint(k) == 0) {
	  u = t;
	}
      }
    }
    if (u == null_eterm) {
      return null_label;
    } else {
      return egraph_term_label(egraph, u);
    }
  }
}




/*
 * Fill in array a with at most n distinct class labels of type tau.
 * If there are fewer than n classes of type tau, then the array is
 * partially filled (in a[0 ... k-1])
 * - return the number of labels k actually stored in a (k <= n)
 */
uint32_t egraph_get_labels_for_type(egraph_t *egraph, type_t tau, elabel_t *a, uint32_t n) {
  uint32_t k, p;
  class_t c;
  eterm_t t;

  assert(n > 0);

  if (is_boolean_type(tau)) {
    if (n == 1) {
      a[0] = true_label;
      return 1;
    } else {
      a[0] = true_label;
      a[1] = false_label;
      return 2;
    }

  } else {

    p = egraph_num_classes(egraph);
    k = 0;
    for (c=0; c<p; c++) {
      if (egraph_class_is_root_class(egraph, c)) {
	t = term_of_occ(egraph_class_root(egraph, c));
	if (egraph_term_real_type(egraph, t) == tau) {
	  assert(k < n);
	  a[k] = pos_label(c);
	  assert(a[k] == egraph_term_label(egraph, t));
	  k ++;
	  if (k == n) break;
	}
      }
    }

    return k;
  }
}



/*
 * Number of classes of type tau in the egraph
 */
uint32_t egraph_num_classes_of_type(egraph_t *egraph, type_t tau) {
  int32_t c, n;
  eterm_t t;
  uint32_t k;

  k = 0;
  n = egraph_num_classes(egraph);
  for (c=0; c<n; c++) {
    if (egraph_class_is_root_class(egraph, c)) {
      t = term_of_occ(egraph_class_root(egraph, c));
      if (egraph_term_real_type(egraph, t) == tau) {
	k ++;
      }
    }
  }

  // for booleans, we double k because of polarity
  if (is_boolean_type(tau)) {
    k *= 2;
  }

  return k;
}



/*
 * Hash and match functions for partition table
 */
static uint32_t hash_arg(egraph_t *egraph, composite_t *c) {
  return hash_arg_signature(c, egraph->terms.label);
}

static bool match_arg(egraph_t *egraph, composite_t *c, composite_t *d) {
  return same_arg_signature(c, d, egraph->terms.label);
}



/*
 * Return the partition structure.
 * Allocate and initialize it if needed.
 */
static ppart_t *egraph_get_app_partition(egraph_t *egraph) {
  ppart_t *pp;

  pp = egraph->app_partition;
  if (pp == NULL) {
    pp = (ppart_t *) safe_malloc(sizeof(ppart_t));
    init_ptr_partition(pp, 0, egraph, (ppart_hash_fun_t) hash_arg, (ppart_match_fun_t) match_arg);
    egraph->app_partition = pp;
  }
  // the pp structure should be empty here
  assert(pp->nelems == 0 && pp->nclasses == 0);

  return pp;
}



/*
 * Build a partition of the (apply ...) terms in the egraph
 * based on argument matches.
 * - scan all composite terms that are (apply ...) and congruence roots
 * - add them one by one to the pp structure
 * - two terms (apply f t_1 ... t_n) and (apply g u_1 ... u_m)
 *   are in the same partition if their aguments are equal in the egraph:
 *   (i.e., n = m and t_1 == u_1 and ... and t_n == u_m)
 * Result:
 * - all non-singleton classes are stored in pp->classes
 *  (cf. ptr_partitions.h and ptr_partitions.c)
 */
void egraph_build_arg_partition(egraph_t *egraph) {
  //  uint32_t i, n;
  uint32_t n;
  composite_t *cmp;
  ppart_t *pp;

  pp = egraph_get_app_partition(egraph);
  n = egraph_num_terms(egraph);
  // test: do this in reverse order
  //  for (i=0; i<n; i++) {
  //    cmp = egraph_term_body(egraph, i);
  while (n > 0) {
    n --;
    cmp = egraph_term_body(egraph, n);
    if (composite_body(cmp) && 
	composite_kind(cmp) == COMPOSITE_APPLY && 
	congruence_table_is_root(&egraph->ctable, cmp, egraph->terms.label)) {
      ptr_partition_add(pp, cmp);
    }
  }
}







/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * Return the value of term occurrence t in the egraph model
 * - the value of all root classes should be available in array value
 */
value_t egraph_get_value(egraph_t *egraph, value_table_t *vtbl, occ_t t) {
  elabel_t l;
  value_t v;

  assert(egraph->mdl.value != NULL && egraph_occ_is_valid(egraph, t));

  l = egraph_label(egraph, t);
  if (is_pos_label(l)) {
    v = egraph->mdl.value[class_of(l)];
  } else if (l == false_label) {
    v = vtbl_mk_false(vtbl);
  } else {
    // this should not happen, but just to be safe we return unknown
    v = vtbl_mk_unknown(vtbl);
  }

  return v;
}



/*
 * Get the type of class c: check the root term's type
 * - if that type is TUPLE/FUNCTION/REAL, the root type may not be 
 *   precise enough, so we check the other elements in the class 
 * - otherwise, return the root type
 */
static type_t egraph_real_type_of_class(egraph_t *egraph, class_t c) {
  type_table_t *types;
  type_t tau, sigma;
  occ_t t, u;

  t = egraph_class_root(egraph, c);
  tau = egraph_term_real_type(egraph, term_of_occ(t));
  assert(tau != NULL_TYPE);

  types = egraph->types;
  switch (type_kind(types, tau)) {
  case REAL_TYPE:
    u = t;
    do {
      // check whether there's an integer object in the class
      u = egraph_next(egraph, u);
      assert(term_of_occ(t) != term_of_occ(u) || t == u);      
      tau = egraph_term_real_type(egraph, term_of_occ(u));
      assert(is_arithmetic_type(tau));
    } while (t != u && is_real_type(tau));
    break;

  case TUPLE_TYPE:
  case FUNCTION_TYPE:
    u = egraph_next(egraph, t);
    while (u != t) {
      // refine the type tau
      // TODO: we could optimize this to avoid creating the
      // intermediate subtypes??
      assert(term_of_occ(t) != term_of_occ(u));      
      sigma = egraph_term_real_type(egraph, term_of_occ(u));
      tau = inf_type(types, tau, sigma);
      assert(tau != NULL_TYPE);
      u = egraph_next(egraph, u);
    }
    break;

  default:
    break;
  }

  return tau;
}


/*
 * Check whether all elements of array a are different from unknown
 * - n = size of the array
 */ 
static bool all_known_values(value_table_t *vtbl, uint32_t n, value_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (object_is_unknown(vtbl, a[i])) {
      return false;
    }
  }
  return true;
}


/*
 * Create a fresh integer using the egraph's internal nat_ctr
 */
static value_t egraph_fresh_nat_value(egraph_t *egraph, value_table_t *vtbl) {
  int32_t k;

  k = egraph->mdl.nat_ctr;
  egraph->mdl.nat_ctr ++;
  return vtbl_mk_int32(vtbl, k);
}



/*
 * Create a fresh bitvector value using the egraph's internal bv_ctr
 * - n = bitsize 
 */
static value_t egraph_fresh_bv_value(egraph_t *egraph, value_table_t *vtbl, uint32_t n) {
  bvconstant_t *bv;
  uint32_t k;

  bv = &egraph->mdl.bv_buffer;
  k = egraph->mdl.bv_ctr ++;
  bvconstant_set_bitsize(bv, n);
  bvconst_set32(bv->data, bv->width, k);
  bvconst_normalize(bv->data, n);

  return vtbl_mk_bv_from_constant(vtbl, bv);
}


/*
 * Create a fresh value of type tau
 */
static value_t make_fresh_value(egraph_t *egraph, value_table_t *vtbl, type_t tau);

// Build a fresh tuple
static value_t make_fresh_tuple(egraph_t *egraph, value_table_t *vtbl, type_t tau) {
  type_table_t *types;
  value_t *aux;
  value_t buffer[10];
  value_t v;
  type_t sigma;
  bool fresh;
  uint32_t i, n;

  types = egraph->types;
  n = tuple_type_arity(types, tau);
  aux = buffer;
  if (n > 10) {
    aux = (value_t *) safe_malloc(n * sizeof(value_t));
  }

  fresh = false;
  for (i=0; i<n; i++) {
    sigma = tuple_type_component(types, tau, i);
    switch (type_kind(types, sigma)) {
    case BOOL_TYPE:
      aux[i] = vtbl_mk_false(vtbl);
      break;

    case SCALAR_TYPE:
      aux[i] = vtbl_mk_const(vtbl, sigma, 0, NULL);
      break;

    default:
      aux[i] = make_fresh_value(egraph, vtbl, sigma);
      if (! object_is_unknown(vtbl, aux[i])) {
	fresh = true;
      }
      break;
    } 
  }

  /*
   * if all children have a reasonable value, construct a tuple
   * otherwise return unknown (we need to make sure that all
   * classes whose value is not unknown have distinct values).
   */
  if (fresh) {
    assert(all_known_values(vtbl, n, aux));
    v = vtbl_mk_tuple(vtbl, n, aux);
  } else {
    v = vtbl_mk_unknown(vtbl);
  }

  if (n > 10) {
    safe_free(aux);
  }

  return v;
}


static value_t make_fresh_value(egraph_t *egraph, value_table_t *vtbl, type_t tau) {
  rational_t *aux;
  bvconstant_t *bv;
  value_t v;
  uint32_t n;

  switch (type_kind(egraph->types, tau)) {
  case INT_TYPE:
  case REAL_TYPE:
    if (egraph->arith_eg == NULL) {
      // no arithmetic solver
      v = egraph_fresh_nat_value(egraph, vtbl);
    } else {
      aux = &egraph->mdl.arith_buffer;
      // try to get a fresh value from the solver
      if (egraph->arith_eg->fresh_value(egraph->th[ETYPE_INT], aux, is_integer_type(tau))) {
	v = vtbl_mk_rational(vtbl, aux);
      } else {
	// solver failed to create a fresh value
	v = vtbl_mk_unknown(vtbl);
      }
    }
    break;

  case BITVECTOR_TYPE:
    n = bv_type_size(egraph->types, tau);    
    if (egraph->bv_eg == NULL) {
      // no bitvector solver
      v = egraph_fresh_bv_value(egraph, vtbl, n);
    } else {
      // get a fresh value from the solver
      bv = &egraph->mdl.bv_buffer;
      if (egraph->bv_eg->fresh_value(egraph->th[ETYPE_BV], bv, n)) {
	v = vtbl_mk_bv_from_constant(vtbl, bv);
      } else {
	v = vtbl_mk_unknown(vtbl);
      }
    }
    break;

  case UNINTERPRETED_TYPE:
    // new constant (anonymous)
    v = vtbl_mk_unint(vtbl, tau, NULL);
    break;

  case TUPLE_TYPE:
    // build a fresh tuple
    v = make_fresh_tuple(egraph, vtbl, tau);
    break;

  case FUNCTION_TYPE:
    // build a fresh function (if possible)
    v = vtbl_mk_unknown(vtbl);
    break;

  case BOOL_TYPE:
  case SCALAR_TYPE:
    // finite types so we can't create a fresh value for sure
    v = vtbl_mk_unknown(vtbl);
    break;

  case UNUSED_TYPE:
  default:
    // should not happen
    assert(false);
    v = vtbl_mk_unknown(vtbl);
    break;
  }

  return v;
}


/*
 * Get the value of class c and store it in egraph->mdl.value[c]
 * (used recursively in egraph_value_of_tuple_class).
 */
static value_t egraph_value_of_class(egraph_t *egraph, value_table_t *vtbl, class_t c);


/*
 * Convert an abstract value (particle x) to a concrete value
 * - the particle is from egraph->mdl.pstore
 * - x must be either a labeled particle of a fresh particle (not a tuple)
 */
static value_t egraph_concretize_value(egraph_t *egraph, value_table_t *vtbl, particle_t x) {
  pstore_t *pstore;
  value_t v;
  elabel_t l;

  pstore = egraph->mdl.pstore;
  v = particle_concrete_value(pstore, x);
  if (v == null_value) {
    switch (particle_kind(pstore, x)) {
    case LABEL_PARTICLE:
      l = particle_label(pstore, x);
      if (is_pos_label(l)) {
	v = egraph_value_of_class(egraph, vtbl, class_of(l));
      } else if (l == false_label) {
	v  = vtbl_mk_false(vtbl);
      } else {
	// should not happen
	assert(false);
	v = vtbl_mk_unknown(vtbl);
      }
      break;

    case FRESH_PARTICLE:
      v = make_fresh_value(egraph, vtbl, fresh_particle_type(pstore, x));
      break;

    default:
      assert(false);
      abort();
    }
    pstore_make_concrete(pstore, x, v);
  }
  return v;
}


/*
 * Concretize a tuple particle x
 * - the result is stored as n concrete values in v[0 ... n-1]
 * - the tuple must have n components
 */
static void egraph_concretize_tuple(egraph_t *egraph, value_table_t *vtbl, particle_t x, uint32_t n, value_t *v) {
  particle_tuple_t *tuple;
  uint32_t i;

  tuple = tuple_particle_desc(egraph->mdl.pstore, x);
  assert(tuple->nelems == n);
  for (i=0; i<n; i++) {
    v[i] = egraph_concretize_value(egraph, vtbl, tuple->elem[i]);
  }
}



/*
 * Conversion of a map of abstract values to a function object
 * - map = the function map (abstract)
 * - tau = function type
 *
 * For every element [idx -> val] of map, we add the mapping (f i) = v to f.
 * where i = concretization of idx and v = concretization of val
 */
static value_t egraph_concretize_map(egraph_t *egraph, value_table_t *vtbl, map_t *map, type_t tau) {
  value_t *aux;
  value_t buffer[10];
  value_t *all_maps;
  value_t v;
  uint32_t i, n, m;

  n = function_type_arity(egraph->types, tau);
  m = map->nelems;

  all_maps = (value_t *) safe_malloc(m * sizeof(value_t));

  if (n == 1) {
    for (i=0; i<m; i++) {
      buffer[0] = egraph_concretize_value(egraph, vtbl, map->data[i].index);
      v = egraph_concretize_value(egraph, vtbl, map->data[i].value);
      all_maps[i] = vtbl_mk_map(vtbl, 1, buffer, v);
    }
  } else {
    aux = buffer;
    if (n > 10) {
      aux = (value_t *) safe_malloc(n * sizeof(value_t));
    }

    for (i=0; i<m; i++) {
      egraph_concretize_tuple(egraph, vtbl, map->data[i].index, n, aux);
      v = egraph_concretize_value(egraph, vtbl, map->data[i].value);
      all_maps[i] = vtbl_mk_map(vtbl, n, aux, v);
    }
    
    if (n > 10) {
      safe_free(aux);
    }
  }

  // get the default value
  if (map->def != null_particle) {
    v = egraph_concretize_value(egraph, vtbl, map->def);
  } else {
    v = vtbl_mk_unknown(vtbl);
  }

  // build the function
  v = vtbl_mk_function(vtbl, tau, m, all_maps, v, NULL); // name = NULL

  safe_free(all_maps);

  return v;
}






/*
 * Value for an arithmetic class c.
 * c must have etype INT or REAL
 */
static value_t egraph_value_of_arith_class(egraph_t *egraph, value_table_t *vtbl, class_t c) {
  rational_t *aux;
  thvar_t x;
  value_t v;

  assert(egraph_class_type(egraph, c) == ETYPE_INT || egraph_class_type(egraph, c) == ETYPE_REAL);

  x = egraph_class_thvar(egraph, c);
  if (x == null_thvar) {
    // there's no arithmetic solver
    assert(egraph->arith_smt == NULL);
    v = egraph_fresh_nat_value(egraph, vtbl);
  } else {
    // there must be an arithmetic solver and it must have assigned a value to x
    aux = &egraph->mdl.arith_buffer;
    if (egraph->arith_eg->value_in_model(egraph->th[ETYPE_INT], x, aux)) {
      v = vtbl_mk_rational(vtbl, aux);
    } else {
      v = vtbl_mk_unknown(vtbl);
    }
  } 
  return v;
}


/*
 * Value for a bitvector class c.
 * c must have etype BV
 */
static value_t egraph_value_of_bv_class(egraph_t *egraph, value_table_t *vtbl, class_t c) {
  bvconstant_t *bv;
  thvar_t x;
  value_t v;
  uint32_t n;
  type_t tau;

  assert(egraph_class_type(egraph, c) == ETYPE_BV);
  x = egraph_class_thvar(egraph, c);
  if (x == null_thvar) {
    // no bitvector solver
    assert(egraph->bv_smt == NULL);
    tau = egraph_real_type_of_class(egraph, c);
    n = bv_type_size(egraph->types, tau);
    v = egraph_fresh_bv_value(egraph, vtbl, n);
  } else {
    // there must be a bitvector solver and it must have assigned a value to x
    bv = &egraph->mdl.bv_buffer;
    if (egraph->bv_eg->value_in_model(egraph->th[ETYPE_BV], x, bv)) {
      v = vtbl_mk_bv_from_constant(vtbl, bv);
    } else {
      v = vtbl_mk_unknown(vtbl);
    }
  }

  return v;
}

/*
 * Value for a tuple class c
 * c must have etype TUPLE
 */
static value_t egraph_value_of_tuple_class(egraph_t *egraph, value_table_t *vtbl, class_t c) {
  composite_t *cmp;
  value_t *aux;
  value_t buffer[10];
  value_t v;
  eterm_t x;
  elabel_t l;
  uint32_t i, n;

  assert(egraph_class_type(egraph, c) == ETYPE_TUPLE);
  x = egraph_class_thvar(egraph, c);
  if (x != null_eterm) {
    /*
     * x is a (tuple ...) composite in the class
     */
    cmp = egraph_term_body(egraph, x);
    assert(cmp != NULL && composite_body(cmp) && composite_kind(cmp) == COMPOSITE_TUPLE);

    n = composite_arity(cmp);
    aux = buffer;
    if (n > 10) {
      aux = (value_t *) safe_malloc(n * sizeof(value_t));
    }

    // recursively get a value for all the children classes
    for (i=0; i<n; i++) {
      l = egraph_label(egraph, composite_child(cmp, i));
      if (is_pos_label(l)) {
	aux[i] = egraph_value_of_class(egraph, vtbl, class_of(l));
      } else if (l == false_label) {
	aux[i] = vtbl_mk_false(vtbl);
      } else {
	// should not happen if all boolean terms have a value
	assert(false);
	aux[i] = vtbl_mk_unknown(vtbl);
      }
    }

    /*
     * if all children have a reasonable value, construct a tuple
     * otherwise return unknown (we need to make sure that all
     * classes whose value is not unknown have distinct values).
     */
    if (all_known_values(vtbl, n, aux)) {
      v = vtbl_mk_tuple(vtbl, n, aux);
    } else {
      v = vtbl_mk_unknown(vtbl);
    }

    if (n > 10) {
      safe_free(aux);
    }
  } else {
    // No theory variable attached to the class 
    // so there are no explicit (tuple ...) in the class
    v = make_fresh_tuple(egraph, vtbl, egraph_real_type_of_class(egraph, c));
  }

  return v;
}



/*
 * Convert composite p to a mapping object
 * - p must be (apply f a[0] .. a[n-1])
 * - we construct the mapping object (v[0] ... v[n-1] |-> r)
 *   where v[i] = value of a[i]
 *            r = value of class of p
 */
static value_t egraph_composite_value(egraph_t *egraph, value_table_t *vtbl, composite_t *p) {
  value_t *aux;
  value_t buffer[10];
  elabel_t l;
  value_t v;
  uint32_t i, n;

  assert(composite_kind(p) == COMPOSITE_APPLY);
  n = composite_arity(p);
  assert(n >= 2);
  n --;

  aux = buffer;
  if (n > 10) {
    aux = (value_t *) safe_malloc(n * sizeof(value_t));
  }

  // values of a[0] ... a[n-1]
  for (i=0; i<n; i++) {
    l = egraph_label(egraph, composite_child(p, i+1));
    if (is_pos_label(l)) {
      aux[i] = egraph_value_of_class(egraph, vtbl, class_of(l));
    } else if (l == false_label) {
      aux[i] = vtbl_mk_false(vtbl);
    } else {
      assert(false);
      aux[i] = vtbl_mk_unknown(vtbl);
    }
  }

  // value of p
  l = egraph_label(egraph, pos_occ(p->id));
  if (is_pos_label(l)) {
    v = egraph_value_of_class(egraph, vtbl, class_of(l));
  } else if (l == false_label) {
    v = vtbl_mk_false(vtbl);
  } else {
    assert(false);
    v = vtbl_mk_unknown(vtbl);
  }

  // build the mapping object [aux[0] ... aux[n-1] -> v] 
  if (all_known_values(vtbl, n, aux) && !object_is_unknown(vtbl, v)) {
    v = vtbl_mk_map(vtbl, n, aux, v);
  } else {
    v = vtbl_mk_unknown(vtbl);
  }
  
  if (n > 10) {
    safe_free(aux);
  }
  
  return v;
}


/*
 * Build a mapping from the composite terms in c's parent vector
 * - tau = type of class c
 */
static value_t egraph_make_fun_value(egraph_t *egraph, value_table_t *vtbl, class_t c, type_t tau) {
  use_vector_t *u;
  composite_t *p;
  occ_t g;
  uint32_t i, n, j;
  value_t *all_maps;
  value_t v;

  u = egraph_class_parents(egraph, c);
  n = u->last;

  assert(n < VTBL_MAX_MAP_SIZE);
  all_maps = safe_malloc(n * sizeof(value_t));

  j = 0;
  for (i=0; i<n; i++) {
    p = u->data[i];
    if (valid_entry(p) && composite_kind(p) == COMPOSITE_APPLY) {
      g = composite_child(p, 0); // function term of p
      if (egraph_class(egraph, g) == c) {
	all_maps[j] = egraph_composite_value(egraph, vtbl, p);
	j ++;
      }
    }
  }

  // function: no default value, no name
  if (all_known_values(vtbl, j, all_maps)) {
    v = vtbl_mk_function(vtbl, tau, j, all_maps, vtbl_mk_unknown(vtbl), NULL);
  } else {
    v = vtbl_mk_unknown(vtbl);
  }

  safe_free(all_maps);

  return v;
}



/*
 * Value for a array/function class c.
 * c must have etype FUNCTION
 */
static value_t egraph_value_of_fun_class(egraph_t *egraph, value_table_t *vtbl, class_t c) {
  map_t *map;
  thvar_t x;
  value_t v;
  type_t tau;

  assert(egraph_class_type(egraph, c) == ETYPE_FUNCTION);
  x = egraph_class_thvar(egraph, c);
  tau = egraph_real_type_of_class(egraph, c);
  if (x == null_thvar) {
    /*
     * no array/function solver: create a new function
     * using the composites terms in c's parent vector
     */
    v = egraph_make_fun_value(egraph, vtbl, c, tau);
  } else {
    /*
     * there is a function solver and it must have assigned a value to x
     */
    assert(egraph->fun_eg != NULL);
    map = egraph->fun_eg->value_in_model(egraph->th[ETYPE_FUNCTION], x);
    if (map != NULL) {
      v = egraph_concretize_map(egraph, vtbl, map, tau);
    } else {
      v = vtbl_mk_unknown(vtbl);
    }
  }

  return v;
}


/*
 * Value of an uninterpreted class c
 * c must have etype NONE
 */
static value_t egraph_value_of_uninterpreted_class(egraph_t *egraph, value_table_t *vtbl, class_t c) {
  occ_t root;
  eterm_t t;
  type_t tau;
  value_t v;
  
  /* 
   * Search for a constant t in the class. If there's none
   * create an anonmymous uninterpreted constant/
   */
  root = egraph_class_root(egraph, c);
  assert(is_pos_occ(root));
  tau = egraph_term_real_type(egraph, term_of_occ(root));
  assert(tau != NULL_TYPE);

  if ((egraph->classes.dmask[c] & 0x1) != 0) {
    // the class contains a constant
    t = term_of_occ(root);
    while (! constant_body(egraph_term_body(egraph, t))) {
      t = term_of_occ(egraph->terms.next[t]);
      assert(t != term_of_occ(root)); // make sure we don't loop forever
    }

    // v = constant of type tau and same id as t, no name
    v = vtbl_mk_const(vtbl, tau, constant_body_id(egraph_term_body(egraph, t)), NULL);

  } else {

    // fresh anonymous constant 
    v = vtbl_mk_unint(vtbl, tau, NULL);
  }

  return v;
}


/*
 * Get the value of class c and store it in egraph->mdl.value[c]
 */
static value_t egraph_value_of_class(egraph_t *egraph, value_table_t *vtbl, class_t c) {
  value_t v;

  v = egraph->mdl.value[c]; 
  if (v == null_value) {
    switch (egraph_class_type(egraph, c)) {
    case ETYPE_INT:
    case ETYPE_REAL:
      v = egraph_value_of_arith_class(egraph, vtbl, c);
      break;

    case ETYPE_FUNCTION:
      v = egraph_value_of_fun_class(egraph, vtbl, c);
      break;

    case ETYPE_BV:
      v = egraph_value_of_bv_class(egraph, vtbl, c);
      break;

    case ETYPE_BOOL:
      /*
       * If all literals are assigned in the core, then all the boolean terms are in
       * the bool_constant_class. So the value[c] must be true.
       */
      assert(c == bool_constant_class &&
	     bvar_value(egraph->core, egraph_class_thvar(egraph, c)) == VAL_TRUE);
      v = vtbl_mk_true(vtbl);
      break;

    case ETYPE_TUPLE:
      v = egraph_value_of_tuple_class(egraph, vtbl, c);
      break;

    case ETYPE_NONE:
      v = egraph_value_of_uninterpreted_class(egraph, vtbl, c);
      break;

    default:
      /*
       * Should not happen
       */
      assert(false);
      v = vtbl_mk_unknown(vtbl);
      break;
    }

    egraph->mdl.value[c] = v;
  }

  return v;
}


/*
 * Assign a value to all the root classes
 */
static void egraph_model_for_root_classes(egraph_t *egraph, value_table_t *vtbl) {
  uint32_t i, n;
  class_t c;

  n = egraph_num_terms(egraph);
  for (i=0; i<n; i++) {
    c = egraph_term_class(egraph, i); // c = root class of term i
    if (egraph->mdl.value[c] == null_value) {
      (void) egraph_value_of_class(egraph, vtbl, c);
    }
  }
}





/*
 * Build a model: the model maps egraph classes to objects built in vtbl 
 */
void egraph_build_model(egraph_t *egraph, value_table_t *vtbl) {
  uint32_t i, n;
  pstore_t *pstore;

  /*
   * Initialize the mdl structure
   */
  egraph->mdl.nat_ctr = 0;
  egraph->mdl.bv_ctr = 0;

  /*
   * Allocate and initialize the value array
   */
  n = egraph->classes.nclasses;
  egraph->mdl.value = (value_t *) safe_malloc(n * sizeof(value_t));
  for (i=0; i<n; i++) {
    egraph->mdl.value[i] = null_value;
  }

  /*
   * Allocate and initialize the pstore then build the
   * array models
   */
  if (egraph->fun_eg != NULL) {
    pstore = (pstore_t *) safe_malloc(sizeof(pstore_t));
    egraph->mdl.pstore = pstore;
    init_pstore(pstore, egraph->types);
    egraph->fun_eg->build_model(egraph->th[ETYPE_FUNCTION], pstore);
  }

  // assign a value to all root classes
  egraph_model_for_root_classes(egraph, vtbl);
}



/*
 * Free/reset internal structures
 */
void egraph_free_model(egraph_t *egraph) {
  if (egraph->fun_eg != NULL) {
    egraph->fun_eg->free_model(egraph->th[ETYPE_FUNCTION]);
  }
  reset_egraph_model(&egraph->mdl);
}




