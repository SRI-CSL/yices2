/*
 * STREAMLINED SAT SOLVER FOR BITBLASTING
 *
 * (TEMPORARY SOLUTION, MAY NEED SOMETHING BETTER)
 */

#include <assert.h>
#include <stddef.h>
#include <float.h>

#include "memalloc.h"
#include "int_array_sort.h"
#include "prng.h"

#include "bit_solver.h"


#define TRACE 0

#if TRACE

#include <stdio.h>
#include <inttypes.h>

#endif


/********************************
 * CLAUSES AND LEARNED CLAUSES  *
 *******************************/

/*
 * Get first watched literal of cl
 */
static inline literal_t get_first_watch(clause_t *cl) {
  return cl->cl[0];
}

/*
 * Get second watched literal of cl
 */
static inline literal_t get_second_watch(clause_t *cl) {
  return cl->cl[1];
}

/*
 * Get watched literal of index (1 - i) in cl.
 * \param i = 0 or 1
 */
static inline literal_t get_other_watch(clause_t *cl, uint32_t i) {
  // flip low-order bit of i
  return cl->cl[i ^ 1];
}

/*
 * Get pointer to learned_clause in which clause cl is embedded. 
 */
static inline learned_clause_t *learned(clause_t *cl) {
  return (learned_clause_t *)(((char *)cl) - offsetof(learned_clause_t, clause));
}

/*
 * Activity of a learned clause
 */
static inline float get_activity(clause_t *cl) {
  return learned(cl)->activity;
}

/*
 * Set the activity to act
 */
static inline void set_activity(clause_t *cl, float act) {
  learned(cl)->activity = act;
}

/*
 * Increase the activity of a learned clause by delta
 */
static inline void increase_activity(clause_t *cl, float delta) {
  learned(cl)->activity += delta;
}

/*
 * Multiply activity by scale
 */
static inline void multiply_activity(clause_t *cl, float scale) {
  learned(cl)->activity *= scale;
}

/*
 * Mark a clause cl for removal
 */
static inline void mark_for_removal(clause_t *cl) {
  cl->cl[0] = - cl->cl[0];
  cl->cl[1] = - cl->cl[1];
}

static inline bool is_clause_to_be_removed(clause_t *cl) {
  return cl->cl[0] < 0 || cl->cl[1] < 0;
}

/*
 * Restore a removed clause: flip the signs back
 */
static inline void restore_removed_clause(clause_t *cl) {
  cl->cl[0] = - cl->cl[0];
  cl->cl[1] = - cl->cl[1];  
}


/*
 * Clause length
 */
static uint32_t clause_length(clause_t *cl) {
  literal_t *a;

  a = cl->cl + 2;
  while (*a >= 0) {
    a ++;
  }

  return a - cl->cl;
}

/*
 * Allocate and initialize a new clause (not a learned clause)
 * \param len = number of literals
 * \param lit = array of len literals
 * The watched pointers are not initialized
 */
static clause_t *new_clause(uint32_t len, literal_t *lit) {
  clause_t *result;
  uint32_t i;

  result = (clause_t *) safe_malloc(sizeof(clause_t) + sizeof(literal_t) + 
				    len * sizeof(literal_t));

  for (i=0; i<len; i++) {
    result->cl[i] = lit[i];
  }
  result->cl[i] = end_clause; // end marker: not a learned clause

  return result;
}

/*
 * Delete clause cl
 * cl must be a non-learned clause, allocated via the previous function.
 */
static inline void delete_clause(clause_t *cl) {
  safe_free(cl);
}

/*
 * Allocate and initialize a new learned clause
 * \param len = number of literals
 * \param lit = array of len literals
 * The watched pointers are not initialized. 
 * The activity is initialized to 0.0
 */
static clause_t *new_learned_clause(uint32_t len, literal_t *lit) {
  learned_clause_t *tmp;
  clause_t *result;
  uint32_t i;

  tmp = (learned_clause_t *) safe_malloc(sizeof(learned_clause_t) + sizeof(literal_t) + 
					 len * sizeof(literal_t));
  tmp->activity = 0.0;
  result = &(tmp->clause);

  for (i=0; i<len; i++) {
    result->cl[i] = lit[i];
  }
  result->cl[i] = end_learned; // end marker: learned clause

  return result;
}

/*
 * Delete learned clause cl
 * cl must have been allocated via the new_learned_clause function
 */
static inline void delete_learned_clause(clause_t *cl) {
  safe_free(learned(cl));
}



/********************
 *  CLAUSE VECTORS  *
 *******************/

/*
 * Create a clause vector of capacity n. 
 */
static clause_t **new_clause_vector(uint32_t n) {
  clause_vector_t *tmp;

  tmp = (clause_vector_t *) safe_malloc(sizeof(clause_vector_t) + n * sizeof(clause_t *));
  tmp->capacity = n;
  tmp->size = 0;

  return tmp->data;
}

/*
 * Clean up: free memory used by v
 */
static void delete_clause_vector(clause_t **v) {
  safe_free(cv_header(v));
}

/*
 * Add clause cl at the end of vector *v. Assumes *v has been initialized.
 */
static void add_clause_to_vector(clause_t ***v, clause_t *cl) {
  clause_vector_t *vector;
  clause_t **d;  
  uint32_t i, n;

  d = *v;
  vector = cv_header(d);
  i = vector->size;
  if (i == vector->capacity) {
    n = i + 1;
    n += (n >> 1); // n = new capacity
    if (n > MAX_CLAUSE_VECTOR_SIZE) {
      out_of_memory();
    }
    vector = (clause_vector_t *) 
      safe_realloc(vector, sizeof(clause_vector_t) + n * sizeof(clause_t *));
    vector->capacity = n;
    d = vector->data;
    *v = d;
  }
  d[i] = cl;
  vector->size = i+1;
}


/*
 * Reset clause vector v: set its size to 0
 */
static inline void reset_clause_vector(clause_t **v) {
  set_cv_size(v, 0);
}


#if 0

// NOT USED?
/*
 * Shrink clause vector *v: attempt to resize *v so that size = capacity.
 * We don't use safe_realloc here since we can keep going and hope for the best 
 * if realloc fails.
 */
static void shrink_clause_vector(clause_t ***v) {
  clause_vector_t *vector;
  uint32_t n;

  vector = cv_header(*v);
  n = vector->size;
  if (n < vector->capacity) {
    vector = realloc(vector, sizeof(clause_vector_t) + n * sizeof(clause_t *));    
    // if vector == NULL, realloc has failed but v is still usable.
    if (vector != NULL) {
      vector->capacity = n;
      *v = vector->data;
    }
  }
}

#endif



/**********************
 *  LITERAL VECTORS   *
 *********************/

/*
 * When used to store binary clauses literal vectors are initially
 * NULL.  Memory is allocated on the first addition and literal
 * vectors are terminated by -1.
 *
 * For a vector v of size i, the literals are stored 
 * in v[0],...,v[i-1], and v[i] = -1
 */

/*
 * Add literal l at the end of vector *v
 * - allocate a fresh vector if *v == NULL
 * - resize *v if *v is full.
 * - add -1 terminator after l.
 */
static void add_literal_to_vector(literal_t **v, literal_t l) {
  literal_vector_t *vector;
  literal_t *d;
  uint32_t i, n;

  d = *v;
  if (d == NULL) {
    i = 0;
    n = DEF_LITERAL_VECTOR_SIZE;
    vector = (literal_vector_t *)
      safe_malloc(sizeof(literal_vector_t) + n * sizeof(literal_t));
    vector->capacity = n;
    d = vector->data;
    *v = d;
  } else {
    vector = lv_header(d);
    i = vector->size;
    n = vector->capacity;
    if (i >= n - 1) {
      n ++;
      n += n>>1; // new cap = 50% more than old capacity
      if (n > MAX_LITERAL_VECTOR_SIZE) {
	out_of_memory();
      }
      vector = (literal_vector_t *) 
	safe_realloc(vector, sizeof(literal_vector_t) + n * sizeof(literal_t));
      vector->capacity = n;
      d = vector->data;
      *v = d;
    }
  }

  assert(i + 1 < vector->capacity);
  
  d[i] = l;
  d[i+1] = null_literal;
  vector->size = i+1;
}


/*
 * Delete literal vector v
 */
static inline void delete_literal_vector(literal_t *v) {
  if (v != NULL) {
    safe_free(lv_header(v));
  }
}


/*
 * Remove the last literal from vector v
 */
static inline void literal_vector_pop(literal_t *v) {
  uint32_t i;

  i = get_lv_size(v);
  assert(i > 0);
  i --;
  v[i] = null_literal;
  set_lv_size(v,  i);
}


/*
 * Last element of vector v (used in assert)
 */
static inline literal_t last_lv_elem(literal_t *v) {
  assert(v != NULL && get_lv_size(v) > 0);
  return v[get_lv_size(v) - 1];
}



/***********
 *  STACK  *
 **********/

/*
 * Initialize stack s for nvar
 */
static void init_stack(prop_stack_t *s, uint32_t nvar) {
  s->lit = (literal_t *) safe_malloc(nvar * sizeof(literal_t));
  s->level_index = (uint32_t *) safe_malloc(DEFAULT_NLEVELS * sizeof(uint32_t));
  s->level_index[0] = 0;
  s->top = 0;
  s->prop_ptr = 0;
  s->theory_ptr = 0;
  s->nlevels = DEFAULT_NLEVELS;
}

/*
 * Extend the size: nvar = new size
 */
static void extend_stack(prop_stack_t *s, uint32_t nvar) {
  s->lit = (literal_t *) safe_realloc(s->lit, nvar * sizeof(literal_t));
}

/*
 * Extend the level_index array by 50%
 */
static void increase_stack_levels(prop_stack_t *s) {
  uint32_t n;

  n = s->nlevels;
  n += n>>1;
  s->level_index = (uint32_t *) safe_realloc(s->level_index, n * sizeof(uint32_t));
  s->nlevels = n;
}

/*
 * Free memory used by stack s 
 */
static void delete_stack(prop_stack_t *s) {
  free(s->lit);
  free(s->level_index);
}

/*
 * Push literal l on top of stack s
 */
static inline void push_literal(prop_stack_t *s, literal_t l) {
  uint32_t i;
  i = s->top;
  s->lit[i] = l;
  s->top = i + 1;
}




/**********
 *  HEAP  *
 *********/

/*
 * Initialize heap for n variables
 * - heap is initially empty: heap_last = 0
 * - heap[0] = -1 is a marker, with activity[-1] higher 
 *   than any variable activity.
 * - activity increment and threshold are set to their
 *   default initial value.
 */
static void init_heap(var_heap_t *heap, uint32_t n) {
  uint32_t i;
  double *tmp;

  heap->size = n;
  tmp = (double *) safe_malloc((n+1) * sizeof(double));
  heap->activity = tmp + 1;
  heap->heap_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  heap->heap = (bvar_t *) safe_malloc((n+1) * sizeof(bvar_t));

  for (i=0; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }

  heap->activity[-1] = DBL_MAX;
  heap->heap[0] = -1;
  heap->heap_last = 0;

  heap->act_increment = INIT_VAR_ACTIVITY_INCREMENT;
  heap->inv_act_decay = 1/VAR_DECAY_FACTOR;
}

/*
 * Extend the heap for n variables
 */
static void extend_heap(var_heap_t *heap, uint32_t n) {
  uint32_t old_size, i;
  double *tmp;

  old_size = heap->size;
  assert(old_size < n);
  heap->size = n;
  tmp = heap->activity - 1;
  tmp = (double *) safe_realloc(tmp, (n+1) * sizeof(double));
  heap->activity = tmp + 1;
  heap->heap_index = (int32_t *) safe_realloc(heap->heap_index, n * sizeof(int32_t));
  heap->heap = (int32_t *) safe_realloc(heap->heap, (n+1) * sizeof(int32_t));

  for (i=old_size; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }
}

/*
 * Free the heap
 */
static void delete_heap(var_heap_t *heap) {
  safe_free(heap->activity - 1);
  safe_free(heap->heap_index);
  safe_free(heap->heap);
}



/*
 * Move x up in the heap.
 * i = current position of x in the heap (or heap_last if x is being inserted)
 */
static inline void update_up(var_heap_t *heap, bvar_t x, uint32_t i) {
  double ax, *act;
  int32_t *index;
  bvar_t *h, y;
  uint32_t j;

  h = heap->heap;
  index = heap->heap_index;
  act = heap->activity;

  ax = act[x];

  j = i >> 1;    // parent of i
  y = h[j];      // variable at position j in the heap

  // The loop terminates since act[h[0]] = DBL_MAX 
  while (act[y] < ax) {
    // move y down, into position i
    h[i] = y;
    index[y] = i;

    // move i and j up
    i = j;
    j >>= 1;
    y = h[j];
  }

  // i is the new position for variable x
  h[i] = x;
  index[x] = i;  
}


/*
 * Remove element at index i in the heap.
 * Replace it by the current last element.
 */
static inline void update_down(var_heap_t *heap, uint32_t i) {
  double ax, *act;
  int32_t* index; 
  bvar_t *h, x, y;
  uint32_t j, last;

  h = heap->heap;
  index = heap->heap_index;
  act = heap->activity;
  last = heap->heap_last;
  heap->heap_last = last - 1;

  assert(i <= last && act[h[i]] >= act[h[last]]);

  if (last == i) return;  // last element was removed

  ax = act[h[last]]; // activity of last heap element.

  j = 2 * i;      // left child of i
  
  while (j + 1 < last) {
    // find child of i with highest activity.
    x = h[j];
    y = h[j+1];
    if (act[y] > act[x]) {
      j++; 
      x = y;
    }

    // x = child of node i of highest activity
    // j = position of x in the heap (j = 2i or j = 2i+1)
    if (ax >= act[x]) {
      // We're done: store last element in position i
      y = h[last];
      h[i] = y;
      index[y] = i;
      return;
    }

    // Otherwise, move x up, into heap[i]
    h[i] = x;
    index[x] = i;

    // go down one step.
    i = j;
    j <<= 1;
  }

  // Final steps: j + 1 >= last:
  // x's position is either i or j.
  y = h[last];
  if (j < last) {
    x = h[j];
    if (ax >= act[x]) {
      h[i] = y;
      index[y] = i;      
    } else {
      h[i] = x;
      index[x] = i;
      h[j] = y;
      index[y] = j;
    }
  } else {
    h[i] = y;
    index[y] = i;
  }
  
}


/*
 * Insert x into the heap, using its current activity.
 * No effect if x is already in the heap.
 * - x must be between 0 and nvars - 1 
 */
static inline void heap_insert(var_heap_t *heap, bvar_t x) {
  if (heap->heap_index[x] < 0) {
    // x not in the heap
    heap->heap_last ++;
    update_up(heap, x, heap->heap_last);
  }
}



/*
 * Get and remove top element
 * - returns null_bvar (i.e., -1) if the heap is empty.
 */
static inline bvar_t heap_get_top(var_heap_t *heap) {  
  bvar_t top;

  if (heap->heap_last == 0) {
    return null_bvar;
  }

  // remove top element
  top = heap->heap[1];
  heap->heap_index[top] = -1;

  // repair the heap
  update_down(heap, 1);

  return top;
}

/*
 * Rescale variable activities: divide by VAR_ACTIVITY_THRESHOLD
 * \param heap = pointer to a heap structure
 * \param n = number of variables
 */
static void rescale_var_activities(var_heap_t *heap, uint32_t n) {
  uint32_t i;
  double *act;

  heap->act_increment *= INV_VAR_ACTIVITY_THRESHOLD;
  act = heap->activity;
  for (i=0; i<n; i++) {
    act[i] *= INV_VAR_ACTIVITY_THRESHOLD;
  }
}


/*
 * Decay
 */
static inline void decay_var_activities(var_heap_t *heap) {
  heap->act_increment *= heap->inv_act_decay;
}



/************************
 *  STATISTICS RECORD   *
 ***********************/


/*
 * Initialize a statistics record
 */
static void init_statistics(bit_solver_stats_t *stat) {
  stat->restarts = 0;
  stat->simplify_calls = 0;
  stat->reduce_calls = 0;
  stat->decisions = 0;
  stat->random_decisions = 0;
  stat->propagations = 0;
  stat->conflicts = 0;
  stat->prob_literals = 0;
  stat->learned_literals = 0;
  stat->prob_clauses_deleted = 0;
  stat->learned_clauses_deleted = 0;
  stat->bin_clauses_deleted = 0;
  stat->literals_before_simpl = 0;
  stat->subsumed_literals = 0;
}


/*
 * Reset = same thing as init
 */
static inline void reset_statistics(bit_solver_stats_t *stats) {
  init_statistics(stats);
}




/***********************
 *  SOLVER OPERATIONS  *
 **********************/

/*
 * Allocate and initialize a solver
 * n = initial size of the variable arrays
 */
void init_bit_solver(bit_solver_t *solver, uint32_t n) {
  uint32_t lsize;

  if (n >= MAX_VARIABLES) {
    out_of_memory();
  }

  if (n == 0) n = 1;  
  lsize = 2 * n;

  solver->status = STATUS_IDLE;

  solver->nvars = 1;  // the constant is always allocated
  solver->nlits = 2;  // corresponding literals (true/false)
  solver->vsize = n;
  solver->lsize = lsize;

  solver->nb_clauses = 0;
  solver->nb_prob_clauses = 0;
  solver->nb_unit_clauses = 0;
  solver->nb_bin_clauses = 0;

  solver->simplify_bottom = 0;
  solver->simplify_props = 0;
  solver->simplify_threshold = 0;
  solver->aux_literals = 0;
  solver->aux_clauses = 0;
  solver->reduce_threshold = 0;

  solver->decision_level = 0;
  solver->base_level = 0;

  solver->cla_inc = INIT_CLAUSE_ACTIVITY_INCREMENT;
  solver->inv_cla_decay = 1/CLAUSE_DECAY_FACTOR;
  solver->scaled_random = (uint32_t)(VAR_RANDOM_FACTOR * VAR_RANDOM_SCALE);

  // Conflict buffers
  solver->conflict = NULL;
  solver->false_clause = NULL;

  // Auxiliary buffer
  init_ivector(&solver->buffer, DEF_LITERAL_BUFFER_SIZE);
  init_ivector(&solver->buffer2, DEF_LITERAL_BUFFER_SIZE);

  // Clause database
  solver->problem_clauses = new_clause_vector(DEF_CLAUSE_VECTOR_SIZE);
  solver->learned_clauses = new_clause_vector(DEF_CLAUSE_VECTOR_SIZE);

  // Unit clauses discovered at base levels > 0
  init_ivector(&solver->saved_units, 0);

  // Assumption vectors
  init_ivector(&solver->assumptions, 0);
  init_ivector(&solver->redundant_assumptions, 0);
  
  /*
   * Variable-indexed arrays
   *
   * s->level is indexed from -1 to n-1
   * s->level[-1] = UINT32_MAX (never assigned, marker variable)
   */
  solver->antecedent = (antecedent_t *) safe_malloc(n * sizeof(antecedent_t)); 
  solver->level = (uint32_t *) safe_malloc((n + 1) * sizeof(uint32_t)) + 1;
  solver->mark = allocate_bitvector(n);
  solver->polarity = allocate_bitvector(n);
  solver->level[-1] = UINT32_MAX;

  /* Literal-indexed arrays
   * s->value is indexed form -2 to n-1
   * s->value[-1] = s->value[-2] = VAL_UNDEF (for end-of-clause markers)
   */
  solver->value = (uint8_t *) safe_malloc((lsize + 2) * sizeof(uint8_t)) + 2;
  solver->bin = (literal_t **) safe_malloc(lsize * sizeof(literal_t *));
  solver->watch = (link_t *) safe_malloc(lsize * sizeof(link_t));
  solver->value[-1] = VAL_UNDEF;
  solver->value[-2] = VAL_UNDEF;

  /*
   * Initialize data structures for true/false literals
   */
  assert(bool_const == 0 && true_literal == 0 && false_literal == 1 && solver->nvars > 0);
  solver->level[bool_const] = 0;
  set_bit(solver->mark, bool_const);  // set for all variables assigned at level 0
  solver->value[true_literal] = VAL_TRUE;
  solver->value[false_literal] = VAL_FALSE;
  solver->bin[true_literal] = NULL;
  solver->bin[false_literal] = NULL;
  solver->watch[true_literal] = NULL_LINK;
  solver->watch[false_literal] = NULL_LINK;
  

  // Stack
  init_stack(&solver->stack, n);

  // Heap
  init_heap(&solver->heap, n);

  // Statistics
  init_statistics(&solver->stats);
}


/*
 * Free memory
 */
void delete_bit_solver(bit_solver_t *solver) {
  uint32_t i, n;
  clause_t **cl;

  /* Delete all the clauses */
  cl = solver->problem_clauses;
  n = get_cv_size(cl);
  for (i=0; i<n; i++) {
    delete_clause(cl[i]);
  }  
  delete_clause_vector(cl);
  
  cl = solver->learned_clauses;
  n = get_cv_size(cl);  
  for (i=0; i<n; i++) {
    delete_learned_clause(cl[i]);
  }
  delete_clause_vector(cl);

  delete_ivector(&solver->saved_units);

  // assumption vectors
  delete_ivector(&solver->assumptions);
  delete_ivector(&solver->redundant_assumptions);
  
  // var-indexed arrays
  safe_free(solver->antecedent);
  safe_free(solver->level - 1);
  delete_bitvector(solver->mark);
  delete_bitvector(solver->polarity);

  // delete the literal vectors in the propagation structures
  n = solver->nlits;
  for (i=0; i<n; i++) {
    delete_literal_vector(solver->bin[i]);
  }
  safe_free(solver->value - 2);
  safe_free(solver->bin);
  safe_free(solver->watch);


  solver->antecedent = NULL;
  solver->level = NULL;
  solver->mark = NULL;
  solver->polarity = NULL;
  solver->value = NULL;
  solver->bin = NULL;
  solver->watch = NULL;

  delete_heap(&solver->heap);
  delete_stack(&solver->stack);
  
  delete_ivector(&solver->buffer);
  delete_ivector(&solver->buffer2);
}





/***************************************
 *  ADDITION OF VARIABLES AND CLAUSES  *
 **************************************/

/*
 * Extend solver for new_size
 */
static void bit_solver_extend(bit_solver_t *solver, uint32_t n) {
  uint32_t lsize;

  assert(n >= solver->vsize);

  if (n >= MAX_VARIABLES) {
    out_of_memory();
  }

  lsize = 2 * n;
  solver->vsize = n;
  solver->lsize = lsize;

  solver->antecedent = (antecedent_t *) safe_realloc(solver->antecedent, n * sizeof(antecedent_t));
  solver->level = (uint32_t *) safe_realloc(solver->level - 1, (n + 1) * sizeof(uint32_t)) + 1;
  solver->mark = extend_bitvector(solver->mark, n);
  solver->polarity = extend_bitvector(solver->polarity, n);

  solver->value = (uint8_t *) safe_realloc(solver->value - 2, (lsize + 2) * sizeof(uint8_t)) + 2;
  solver->bin = (literal_t **) safe_realloc(solver->bin, lsize * sizeof(literal_t *));
  solver->watch = (link_t *) safe_realloc(solver->watch, lsize * sizeof(link_t));

  extend_heap(&solver->heap, n);
  extend_stack(&solver->stack, n);
}


/*
 * Add n variables 
 */
void bit_solver_add_vars(bit_solver_t *solver, uint32_t n) {
  uint32_t nvars, new_size, i;
  literal_t l0, l1;

  nvars = solver->nvars;
  if (nvars + n > solver->vsize) {
    new_size = solver->vsize + 1;
    new_size += new_size >> 1;
    if (new_size < nvars + n) {
      new_size = nvars + n;
    }
    bit_solver_extend(solver, new_size);
    assert(nvars + n <= solver->vsize);
  }

  for (i=nvars; i<nvars+n; i++) {
    clr_bit(solver->mark, i);
    clr_bit(solver->polarity, i);  // 0 means negative
    solver->level[i] = UINT32_MAX;
    solver->antecedent[i] = mk_literal_antecedent(null_literal);
    l0 = pos_lit(i);
    l1 = neg_lit(i);
    solver->value[l0] = VAL_UNDEF;
    solver->value[l1] = VAL_UNDEF;
    solver->bin[l0] = NULL;
    solver->bin[l1] = NULL;
    solver->watch[l0] = NULL_LINK;
    solver->watch[l1] = NULL_LINK;
  }

  solver->nvars += n;
  solver->nlits += 2 * n;
}




/*
 * Allocate and return a fresh boolean variable
 */
bvar_t bit_solver_new_var(bit_solver_t *solver) {
  uint32_t new_size, i;
  literal_t l0, l1;

  i = solver->nvars;
  if (i >= solver->vsize) {
    new_size = solver->vsize + 1;
    new_size += new_size >> 1;
    bit_solver_extend(solver, new_size);
    assert(i < solver->vsize);
  }

  clr_bit(solver->mark, i);
  clr_bit(solver->polarity, i);
  solver->level[i] = UINT32_MAX;
  solver->antecedent[i] = mk_literal_antecedent(null_literal);
  l0 = pos_lit(i);
  l1 = neg_lit(i);
  solver->value[l0] = VAL_UNDEF;
  solver->value[l1] = VAL_UNDEF;
  solver->bin[l0] = NULL;
  solver->bin[l1] = NULL;
  solver->watch[l0] = NULL_LINK;
  solver->watch[l1] = NULL_LINK;

  solver->nvars ++;
  solver->nlits += 2;

  return i;
}



/*
 * Assign literal l (at the base level) 
 * --> this means that { l } is a unit clause
 * --> we mark var_of(l) so that l is not considered in the 
 * construction of conflict clauses, unsat cores, or explanations.
 *
 * If the base level is non-zero, we record that l is a unit clause
 * by storing it in saved_unit.
 * (Unit clauses at 
 */
static void assign_literal(bit_solver_t *solver, literal_t l) {
  bvar_t v;

  assert(0 <= l && l < solver->nlits);
  assert(solver->value[l] == VAL_UNDEF);
  assert(solver->decision_level == solver->base_level);

  solver->nb_unit_clauses ++;	

  solver->value[l] = VAL_TRUE;
  solver->value[not(l)] = VAL_FALSE;
  push_literal(&solver->stack, l);

  v = var_of(l);
  solver->level[v] = 0;
  solver->antecedent[v] = mk_literal_antecedent(null_literal);
  set_bit(solver->mark, v); // marked as assigned at level 0
  if (solver->base_level > 0) {
    ivector_push(&solver->saved_units, l);
  }
}


/*
 * Add empty clause: mark the whole thing as unsat
 */
void bit_solver_add_empty_clause(bit_solver_t *solver) {
  solver->status = STATUS_UNSAT;
}

/*
 * Add unit clause { l }: push l on the assignment stack
 * or set status to unsat if l is already false
 */
void bit_solver_add_unit_clause(bit_solver_t *solver, literal_t l) {
  assert(0 <= l && l < solver->nlits);
  switch (solver->value[l]) {
  case VAL_FALSE:
    solver->status = STATUS_UNSAT;
    break;
  case VAL_UNDEF:
    assign_literal(solver, l);
    break;
  default: // VAL_TRUE: nothing to do
    break;
  }
}

/*
 * Add clause { l0, l1 }
 */
void bit_solver_add_binary_clause(bit_solver_t *solver, literal_t l0, literal_t l1) {
  assert(0 <= l0 && l0 < solver->nlits);
  assert(0 <= l1 && l1 < solver->nlits);

  add_literal_to_vector(solver->bin + l0, l1);
  add_literal_to_vector(solver->bin + l1, l0);

  solver->nb_bin_clauses ++;
}

/*
 * Add an n-literal clause when n >= 3
 */
static void add_clause_core(bit_solver_t *solver, uint32_t n, literal_t *lit) {
  clause_t *cl;
  literal_t l;

#ifndef NDEBUG
  // check that all literals are valid
  uint32_t i;

  for (i=0; i<n; i++) {
    assert(0 <= lit[i] && lit[i] < solver->nlits);
  }
#endif

  cl = new_clause(n, lit);
  add_clause_to_vector(&solver->problem_clauses, cl);

  // set watch literals
  l = lit[0];
  solver->watch[l] = cons(0, cl, solver->watch[l]);

  l = lit[1];
  solver->watch[l] = cons(1, cl, solver->watch[l]);

  // update number of clauses
  solver->nb_prob_clauses ++;
  solver->nb_clauses ++;
  solver->stats.prob_literals += n;
}

/*
 * Add three-literal clause {l0, l1, l2} 
 */
void bit_solver_add_ternary_clause(bit_solver_t *solver, literal_t l0, literal_t l1, literal_t l2) {
  literal_t lit[3];

  lit[0] = l0;
  lit[1] = l1;
  lit[2] = l2;
  add_clause_core(solver, 3, lit);
}


/*
 * Add a clause of n literals
 */
void bit_solver_add_clause(bit_solver_t *solver, uint32_t n, literal_t *lit) {
  if (n > 2) {
    add_clause_core(solver, n, lit);
  } else if (n == 2) {
    bit_solver_add_binary_clause(solver, lit[0], lit[1]);
  } else if (n == 1) {
    bit_solver_add_unit_clause(solver, lit[0]);
  } else {
    bit_solver_add_empty_clause(solver);
  }
}



/*
 * More careful version: simplify a clause and add it to solver. 
 * No effect if sol is already unsat.
 */
void bit_solver_simplify_and_add_clause(bit_solver_t *solver, uint32_t n, literal_t *lit) {
  uint32_t i, j;
  literal_t l, l_aux;

  assert(solver->base_level == 0 && solver->decision_level == 0);

  if (solver->status == STATUS_UNSAT) return;

  if (n == 0) {
    bit_solver_add_empty_clause(solver);
    return;
  }

  /*
   * Remove duplicates and check for opposite literals l, not(l)
   * (sorting ensure that not(l) is just after l)
   */
  int_array_sort(lit, n);  
  l = lit[0];
  j = 1;
  for (i=1; i<n; i++) {
    l_aux = lit[i];
    if (l_aux != l) {
      if (l_aux == not(l)) return; // true clause
      lit[j] = l_aux;
      l = l_aux;
      j ++;
    }
  }
  n = j; // new clause size


  /*
   * Remove false literals/check for a true literal
   */
  j = 0;
  for (i=0; i<n; i++) {
    l = lit[i];
    switch (solver->value[l]) {
    case VAL_FALSE:
      break;
    case VAL_UNDEF:
      lit[j] = l;
      j++;
      break;
    default: // true literal, so the clause is true
      return;
    }
  }
  n = j; // new clause size

  bit_solver_add_clause(solver, n, lit);
}



/**********************************
 *  ADDITION OF LEARNED CLAUSES   *
 *********************************/

/*
 * Rescale activity of all the learned clauses
 * (divide all by CLAUSE_ACTIVITY_THRESHOLD)
 */
static void rescale_clause_activities(bit_solver_t *solver) {
  uint32_t i, n;
  clause_t **v;

  v = solver->learned_clauses;
  n = get_cv_size(v);
  for (i=0; i<n; i++) {
    multiply_activity(v[i], INV_CLAUSE_ACTIVITY_THRESHOLD);
  }
  solver->cla_inc *= INV_CLAUSE_ACTIVITY_THRESHOLD;
}


/*
 * Increase activity of learned clause cl
 * Rescale all activities if clause-activity max threshold is reached
 */
static inline void increase_clause_activity(bit_solver_t *solver, clause_t *cl) {
  increase_activity(cl, solver->cla_inc);
  if (get_activity(cl) > CLAUSE_ACTIVITY_THRESHOLD) {
    rescale_clause_activities(solver);
  }
}


/*
 * Decay
 */
static inline void decay_clause_activities(bit_solver_t *solver) {
  solver->cla_inc *= solver->inv_cla_decay;
}


/*
 * Add an array of literals as a new learned clause
 *
 * Preconditions:
 * - n must be at least 2.
 * - lit[0] must be the literal of highest decision level in the clause.
 * - lit[1] must be a literal with second highest decision level
 */
static clause_t *add_learned_clause(bit_solver_t *solver, uint32_t n, literal_t *lit) {
  clause_t *cl;
  literal_t l;

  // Create and add a new learned clause.
  // Set its activity to current cla_inc
  cl = new_learned_clause(n, lit);
  add_clause_to_vector(&solver->learned_clauses, cl);
  increase_clause_activity(solver, cl);
  
  // insert cl into the watched lists
  l = lit[0];
  solver->watch[l] = cons(0, cl, solver->watch[l]);

  l = lit[1];
  solver->watch[l] = cons(1, cl, solver->watch[l]);

  // increase clause counter
  solver->nb_clauses ++;
  solver->stats.learned_literals += n;

  return cl;
}





/*********************************
 *  DELETION OF LEARNED CLAUSES  *
 ********************************/

/*
 * Reorder an array  a[low ... high-1] of learned clauses so that
 * the clauses are divided in two half arrays:
 * - the clauses of highest activities are all stored in a[low...half - 1]  
 * - the clauses of lowest activities are in a[half ... high-1], 
 * where half = (low + high) / 2.
 */
static void quick_split(clause_t **a, uint32_t low, uint32_t high) {
  uint32_t i, j, half;
  float pivot;
  clause_t *aux;

  if (high <= low + 1) return;

  half = (low + high)/2;

  do {
    i = low;
    j = high;
    pivot = get_activity(a[i]);

    do { j --; } while (get_activity(a[j]) < pivot);
    do { i ++; } while (i <= j && get_activity(a[i]) > pivot);

    while (i < j) {
      // a[i].act <= pivot and a[j].act >= pivot: swap a[i] and a[j]
      aux = a[i];
      a[i] = a[j];
      a[j] = aux;

      do { j--; } while (get_activity(a[j]) < pivot);
      do { i++; } while (get_activity(a[i]) > pivot);
    }

    // a[j].act >= pivot, a[low].act = pivot: swap a[low] and a[i]
    aux = a[low];
    a[low] = a[j];
    a[j] = aux;

    /*
     * at this point:
     * - all clauses in a[low,.., j - 1] have activity >= pivot
     * - activity of a[j] == pivot
     * - all clauses in a[j+1,..., high-1] have activity <= pivot
     * reapply the procedure to whichever of the two subarrays 
     * contains the half point
     */
    if (j < half) {
      low = j + 1;
    } else {
      high = j;
    }    
  } while (j != half);
}


/*
 * Apply this to a vector v of learned_clauses
 */
static inline void reorder_clause_vector(clause_t **v) {
  quick_split(v, 0, get_cv_size(v));
}



/*
 * Auxiliary function: follow clause list 
 * Remove all clauses marked for deletion
 */
static inline void cleanup_watch_list(link_t *list) {
  link_t lnk;
  clause_t *cl;

  for (lnk = *list; lnk != NULL_LINK; lnk = next_of(lnk)) {
    cl = clause_of(lnk);
    if (! is_clause_to_be_removed(cl)) {
      *list = lnk;
      list = cdr_ptr(lnk);
    }
  }
  *list = NULL_LINK; // end of list
}


/*
 * Update all watch lists: remove all clauses marked for deletion.
 */
static void cleanup_watch_lists(bit_solver_t *solver) {
  uint32_t i, n;

  n = solver->nlits;
  for (i=0; i<n; i ++) {
    cleanup_watch_list(solver->watch + i);
  }
}


/*
 * Check whether cl is an antecedent clause
 */
static inline bool clause_is_locked(bit_solver_t *solver, clause_t *cl) {
  literal_t l0, l1;

  l0 = get_first_watch(cl);
  l1 = get_second_watch(cl);
  
  return (solver->value[l0] != VAL_UNDEF && 
	  solver->antecedent[var_of(l0)] == mk_clause0_antecedent(cl))
    || (solver->value[l1] != VAL_UNDEF && 
	solver->antecedent[var_of(l1)] == mk_clause1_antecedent(cl));
}


/*
 * Delete all clauses that are marked for deletion
 */
static void delete_learned_clauses(bit_solver_t *solver) {
  uint32_t i, j, n;
  clause_t **v;

  v = solver->learned_clauses;
  n = get_cv_size(v);

  // clean up all the watch-literal lists
  cleanup_watch_lists(solver);

  // do the real deletion
  solver->stats.learned_literals = 0;

  j = 0;
  for (i = 0; i<n; i++) {
    if (is_clause_to_be_removed(v[i])) {
      delete_learned_clause(v[i]);
    } else {
      solver->stats.learned_literals += clause_length(v[i]);
      v[j] = v[i];
      j ++;
    }
  }

  // set new size of the learned clause vector
  set_cv_size(solver->learned_clauses, j);
  solver->nb_clauses -= (n - j);

  solver->stats.learned_clauses_deleted += (n - j);  
}


/*
 * Delete half the learned clauses, minus the locked ones (Minisat style).
 * This is expensive: the function scans and reconstructs the
 * watched lists.
 */
static void reduce_learned_clause_set(bit_solver_t *solver) {
  uint32_t i, n;
  clause_t **v;
  //  float median_act, act_threshold;
  float act_threshold;

  assert(get_cv_size(solver->learned_clauses) > 0);

  // put the clauses with lowest activity in the upper
  // half of the learned clause vector.
  reorder_clause_vector(solver->learned_clauses);

  v = solver->learned_clauses;
  n = get_cv_size(v);

  //  median_act = get_activity(v[n/2]);
  act_threshold = solver->cla_inc/n;

  //  if (median_act < act_threshold) {
  //    act_threshold = median_act;
  //  }

  // prepare for deletion: all non-locked clauses, with activity less
  // than activitiy_threshold are marked for deletion.
  for (i=0; i<n/2; i++) {
    if (get_activity(v[i]) <= act_threshold && ! clause_is_locked(solver, v[i])) {
      mark_for_removal(v[i]);
    }
  }
  for (i = n/2; i<n; i++) {
    if (! clause_is_locked(solver, v[i])) {
      mark_for_removal(v[i]);
    }
  }

  delete_learned_clauses(solver);
  solver->stats.reduce_calls ++;
}




/******************************************
 *  SIMPLICATION OF THE CLAUSE DATABASE   *
 *****************************************/

/*
 * Simplify clause cl, given the current literal assignment
 * - mark cl for deletion if it's true 
 * - otherwise remove the false literals
 * The watched literals are unchanged.
 *
 * Update the counters aux_clauses and aux_literals if the clause
 * is not marked for removal.
 *
 * This is sound only at level 0.
 */
static void simplify_clause(bit_solver_t *solver, clause_t *cl) {
  uint32_t i, j;
  literal_t l;

  assert(solver->base_level == 0 && solver->decision_level == 0);

  i = 0;
  j = 0;
  do {
    l = cl->cl[i];
    i ++;
    switch (solver->value[l]) {
      //    case VAL_FALSE:
      //      break;

    case VAL_UNDEF:
      cl->cl[j] = l;
      j ++;
      break;

    case VAL_TRUE:
      mark_for_removal(cl);
      return;
    }
  } while (l >= 0);

  solver->aux_literals += j - 1;
  solver->aux_clauses ++;
  // could migrate cl to two-literal if j is 3??
}


/*
 * Check whether cl is true at the base level. If so mark it
 * for removal.
 */
static void mark_true_clause(bit_solver_t *solver, clause_t *cl) {
  uint32_t i;
  literal_t l;

  assert(solver->base_level == solver->decision_level);

  i = 0;
  do {
    l = cl->cl[i];
    i ++;
    if (solver->value[l] == VAL_TRUE) {
      mark_for_removal(cl);
      return;
    }
  } while (l >= 0);

  solver->aux_literals += (i - 1);
  solver->aux_clauses ++;
}




/*
 * Simplify the set of clauses given the current assignment:
 * - remove all clauses that are true from the watched lists 
 * - if we're at level 0, also remove false_literals from the 
 *   problem and learned clauses.
 */
static void simplify_clause_set(bit_solver_t *solver) {
  uint32_t i, j, n;
  clause_t **v;

  assert(solver->decision_level == solver->base_level);

  if (solver->base_level == 0) {
    /*
     * Apply thorough simplifications at level 0
     */
    // simplify problem clauses
    solver->aux_literals = 0;
    solver->aux_clauses = 0;
    v = solver->problem_clauses;
    n = get_cv_size(v);
    for (i=0; i<n; i++) {
      if (! is_clause_to_be_removed(v[i]) && 
	  ! clause_is_locked(solver, v[i])) {
	simplify_clause(solver, v[i]);
      }
    }
    solver->stats.prob_literals = solver->aux_literals;
    solver->nb_prob_clauses = solver->aux_clauses;

    // simplify learned clauses
    solver->aux_literals = 0;
    solver->aux_clauses = 0;
    v = solver->learned_clauses;
    n = get_cv_size(v);
    for (i=0; i<n; i++) {
      assert(! is_clause_to_be_removed(v[i]));
      if (! clause_is_locked(solver, v[i])) {
	simplify_clause(solver, v[i]);
      }
    }
    solver->stats.learned_literals = solver->aux_literals;

  } else {
    /*
     * Mark the true clauses for removal
     */
    // mark the true problem clauses
    solver->aux_literals = 0;
    solver->aux_clauses = 0;
    v = solver->problem_clauses;
    n = get_cv_size(v);
    for (i=0; i<n; i++) {
      if (! is_clause_to_be_removed(v[i]) && 
	  ! clause_is_locked(solver, v[i])) {
	mark_true_clause(solver, v[i]);
      }
    }
    solver->stats.prob_literals = solver->aux_literals;
    solver->nb_prob_clauses = solver->aux_clauses;

    // mark the true learned clauses
    solver->aux_literals = 0;
    v = solver->learned_clauses;
    n = get_cv_size(v);
    for (i=0; i<n; i++) {
      assert(! is_clause_to_be_removed(v[i]));
      if (! clause_is_locked(solver, v[i])) {
	mark_true_clause(solver, v[i]);
      }
    }
    solver->stats.learned_literals = solver->aux_literals;

  }

  /*
   * cleanup the watched literal lists: all marked (i.e., true)
   * clauses are removed from the lists.
   */
  cleanup_watch_lists(solver);

  /*
   * Remove the true simplified problem clauses for good
   * if we're at base_level 0
   */
  if (solver->base_level == 0) {
    v = solver->problem_clauses;
    n = get_cv_size(v);
    j = 0;
    for (i=0; i<n; i++) {
      if (is_clause_to_be_removed(v[i])) {
	delete_clause(v[i]);
      } else {
	v[j] = v[i];
	j ++;
      }
    }
    set_cv_size(v, j);
    solver->nb_clauses -= n - j;
    solver->stats.prob_clauses_deleted += n - j;
  }


  /*
   * Remove the marked (i.e. true) learned clauses for good
   */
  v = solver->learned_clauses;
  n = get_cv_size(v);
  j = 0;
  for (i=0; i<n; i++) {
    if (is_clause_to_be_removed(v[i])) {
      delete_learned_clause(v[i]);
    } else {
      v[j] = v[i];
      j ++;
    }
  }
  set_cv_size(v, j);
  solver->nb_clauses -= n - j;
  solver->stats.learned_clauses_deleted += n - j;
}


/*
 * Clean up a binary-clause vector v
 * - assumes that v is non-null
 * - remove all literals of v that are assigned
 * - for each deleted literal, increment sol->aux_literals.
 * This is sound only at level 0.
 */
static void cleanup_binary_clause_vector(bit_solver_t *solver, literal_t *v) {
  uint32_t i, j;
  literal_t l;

  i = 0;
  j = 0;
  do {
    l = v[i++];
    if (solver->value[l] == VAL_UNDEF) { //keep l
      v[j ++] = l;
    }    
  } while (l >= 0); // end-marker is copied too

  solver->aux_literals += i - j;
  set_lv_size(v, j - 1);
}


/*
 * Simplify all binary vectors affected by the current assignment
 * - scan the literals in the stack from sol->simplify_bottom to sol->stack.top
 * - remove all the binary clauses that contain one such literal
 * - free the binary watch vectors
 * Can be used only at base_level = 0
 */
static void simplify_binary_vectors(bit_solver_t *solver) {
  uint32_t i, j, n;
  literal_t l0, *v0, l1;

  assert(solver->decision_level == 0 && solver->base_level == 0);

  solver->aux_literals = 0;   // counts the number of literals removed
  for (i = solver->simplify_bottom; i < solver->stack.top; i++) {
    l0 = solver->stack.lit[i];

    // remove all binary clauses that contain l0
    v0 = solver->bin[l0];
    if (v0 != NULL) {
      n = get_lv_size(v0);
      for (j=0; j<n; j++) {
	l1 = v0[j];
	if (solver->value[l1] == VAL_UNDEF) {
	  // sol->bin[l1] is non null.
	  assert(solver->bin[l1] != NULL);
	  cleanup_binary_clause_vector(solver, solver->bin[l1]);
	}
      }

      delete_literal_vector(v0);
      solver->bin[l0] = NULL;
      solver->aux_literals += n;
    }

    // remove all binary clauses that contain not(l0)
    l0 = not(l0);
    v0 = solver->bin[l0];
    if (v0 != NULL) {
      solver->aux_literals += get_lv_size(v0);
      delete_literal_vector(v0);
      solver->bin[l0] = NULL;
    }
  }

  solver->aux_literals /= 2;
  solver->stats.bin_clauses_deleted += solver->aux_literals;
  solver->nb_bin_clauses -= solver->aux_literals;

  solver->aux_literals = 0;
}



/*
 * Simplify all the database: problem clauses, learned clauses,
 * and binary clauses.
 * - remove the clauses that are true at the base level from 
 *   the watched lists
 * - if base level is 0, also delete the true problem clauses 
 *   and binary clauses and remove the false literals.
 */
static void simplify_clause_database(bit_solver_t *solver) {
  assert(solver->decision_level == solver->base_level && 
	 solver->stack.top == solver->stack.prop_ptr);

  solver->stats.simplify_calls ++;
  simplify_clause_set(solver);
  if (solver->base_level == 0) {
    simplify_binary_vectors(solver);
  }
}






/****************************************
 *  RESTORATION OF THE CLAUSE DATABASE  *
 ***************************************/

#if 0
/*
 * Mark all learned clauses for removal
 */
static void remove_all_learned_clauses(bit_solver_t *solver) {
  uint32_t i, n;
  clause_t **v;

  v = solver->learned_clauses;
  n = get_cv_size(v);

  for (i=0; i<n; i++) {
    mark_for_removal(v[i]);
  }
}
#endif


/*
 * Reset the watch lists (to empty lists)
 */
static void reset_watch_lists(bit_solver_t *solver) {
  uint32_t i, n;

  n = solver->nlits;
  for (i=0; i<n; i++) {
    solver->watch[i] = NULL_LINK;
  }
}


/*
 * Restore the clause database to what it was when check started:
 * - remove all learned clauses
 * - put back all the deleted problem clauses in the watched lists
 */
static void restore_clause_database(bit_solver_t *solver) {
  uint32_t i, n;
  clause_t **v;
  clause_t *cl;
  literal_t l;

  assert(solver->decision_level == solver->base_level);

#if 0
  // mark the learned clauses for removal ?? not clear that pays off
  remove_all_learned_clauses(solver); 

  // do the real deletion here
  v = solver->learned_clauses;
  n = get_cv_size(v);
  for (i=0; i<n; i++) {
    delete_learned_clause(v[i]);
  }
  reset_clause_vector(v);
#endif

  // empty the watch lists
  reset_watch_lists(solver);


  /*
   * put back all the problem clauses that are marked true
   * into the watched lists
   */
  v = solver->problem_clauses;
  n = get_cv_size(v);
  for (i=0; i<n; i++) {
    cl = v[i];
    if (is_clause_to_be_removed(cl)) {
      // cl has been marked. It's not any more
      restore_removed_clause(cl);
    }

    // put cl back into the watch lists
    l = cl->cl[0];
    assert(0 <= l && l < solver->nlits);
    solver->watch[l] = cons(0, cl, solver->watch[l]);

    l = cl->cl[1];
    assert(0 <= l && l < solver->nlits);
    solver->watch[l] = cons(1, cl, solver->watch[l]);
  }

  solver->nb_prob_clauses = n;
}







/*************************
 *  LITERAL ASSIGNMENT   *
 ***********************/

/*
 * Decide literal: increase decision level then
 * assign literal l to true and push it on the stack
 */
static void bit_solver_decide_literal(bit_solver_t *solver, literal_t l) {
  uint32_t d;
  bvar_t v;

  assert(solver->value[l] == VAL_UNDEF);

  solver->stats.decisions ++;

  // Increase decision level
  d = solver->decision_level + 1;
  solver->decision_level = d;
  if (solver->stack.nlevels <= d) {
    increase_stack_levels(&solver->stack);
  }
  solver->stack.level_index[d] = solver->stack.top;

  solver->value[l] = VAL_TRUE;
  solver->value[not(l)] = VAL_FALSE;
  push_literal(&solver->stack, l);

  v = var_of(l);
  solver->level[v] = d;
  solver->antecedent[v] = mk_literal_antecedent(null_literal);
}


/*
 * Assign literal l to true and attach antecedent a.
 * solver->mark[v] is set if decision level = 0
 */
static void implied_literal(bit_solver_t *solver, literal_t l, antecedent_t a) {
  bvar_t v;

  assert(solver->value[l] == VAL_UNDEF);

  solver->stats.propagations ++;

  solver->value[l] = VAL_TRUE;
  solver->value[not(l)] = VAL_FALSE;
  push_literal(&solver->stack, l);

  v = var_of(l);
  solver->level[v] = solver->decision_level;
  solver->antecedent[v] = a;
  if (solver->decision_level == 0) {
    set_bit(solver->mark, v);
  }
}



/**************************
 *  BOOLEAN PROPAGATION   *
 *************************/

/*
 * Conflict clauses: 
 * - for a general clause cl: record literal array cl->cl 
 *   into sol->conflict and cl itself in sol->false_clause.
 * - for binary or ternary clauses, fake a generic clause:
 *   store literals in conflict_buffer, add terminator -1, and
 *   record a pointer to conflict_buffer.
 */

/*
 * Record a two-literal conflict: clause {l0, l1} is false
 */
static inline void record_binary_conflict(bit_solver_t *solver, literal_t l0, literal_t l1) {
  solver->conflict_buffer[0] = l0;
  solver->conflict_buffer[1] = l1; 
  solver->conflict_buffer[2] = end_clause;
  solver->conflict = solver->conflict_buffer;
}


/*
 * Record cl as a conflict clause
 */
static inline void record_clause_conflict(bit_solver_t *solver, clause_t *cl) {
  solver->false_clause = cl;
  solver->conflict = cl->cl;
}


/*
 * Propagation via binary clauses:
 * - sol = solver
 * - val = literal value array (must be sol->value)
 * - l0 = literal (must be false in the current assignment)
 * - v = array of literals terminated by -1 (must be sol->bin[l])
 * v must be != NULL 
 *
 * Return true if there's no conflict, false otherwise
 */
static bool propagation_via_bin_vector(bit_solver_t *sol, uint8_t *val, literal_t l0, literal_t *v) {
  literal_t l1;
  bval_t v1;

  assert(v != NULL);
  assert(sol->value == val && sol->bin[l0] == v && sol->value[l0] == VAL_FALSE);

  for (;;) {
    // Search for non-true literals in v
    // This terminates since val[end_marker] = VAL_UNDEF
    do {
      l1 = *v ++;
      v1 = val[l1];
    } while (v1 == VAL_TRUE);

    if (l1 < 0) break; // end_marker

    if (v1 == VAL_UNDEF) {
      implied_literal(sol, l1, mk_literal_antecedent(l0));
    } else {
      record_binary_conflict(sol, l0, l1);
      return false;
    }
  }

  return true;
}


/*
 * Propagation via the watched lists of a literal l0.
 * - sol = solver
 * - val = literal value array (must be sol->value)
 * - list = start of the watch list (must be sol->watch + l0)
 *
 * Return true if there's no conflict, false otherwise
 */
static inline bool propagation_via_watched_list(bit_solver_t *sol, uint8_t *val, link_t *list) {
  bval_t v1;
  clause_t *cl;
  link_t link;
  uint32_t k, i;
  literal_t l1, l, *b;

  assert(sol->value == val);

  link = *list;
  while (link != NULL_LINK) {
    cl = clause_of(link);
    i = idx_of(link);
    l1 = get_other_watch(cl, i);
    v1 = val[l1];

    assert(next_of(link) == cl->link[i]);
    assert(cdr_ptr(link) == cl->link + i);

    if (v1 == VAL_TRUE) {
      /*
       * Skip clause cl: it's already true
       */
      *list = link;
      list = cl->link + i;
      link = cl->link[i];

    } else {
      /*
       * Search for a new watched literal in cl.
       * The loop terminates since cl->cl terminates with an end marked 
       * and val[end_marker] == VAL_UNDEF.
       */
      k = 1;
      b = cl->cl;
      do {
	k ++;
	l = b[k];
      } while (val[l] == VAL_FALSE);
      
      if (l >= 0) {
	/*
	 * l occurs in b[k] = cl->cl[k] and is either TRUE or UNDEF
	 * make l a new watched literal
	 * - swap b[i] and b[k]
         * - insert cl into l's watched list (link[i])
	 */
	b[k] = b[i];
	b[i] = l;

	// insert cl in watch[l] list and move to the next clause
	link = cl->link[i];
	sol->watch[l] = cons(i, cl, sol->watch[l]);

      } else {
	/*
	 * All literals of cl, except possibly l1, are false
	 */
	if (v1 == VAL_UNDEF) {
	  // l1 is implied
	  implied_literal(sol, l1, mk_clause_antecedent(cl, i^1));

	  // move to the next clause
	  *list = link;
	  list = cl->link + i;
	  link = cl->link[i];

	} else {
	  // v1 == VAL_FALSE: conflict found
	  record_clause_conflict(sol, cl);
	  *list = link;
	  return false;
	}
      }
    }
  }

  *list = NULL_LINK;

  return true;
}


/*
 * Full propagation: until either the propagation queue is empty,
 * or a conflict is found
 * - return true if there's no conflict, false otherwise
 */
static bool propagation(bit_solver_t *sol) {
  uint8_t *val;
  literal_t *queue;
  literal_t l, *bin;
  // uint32_t i, j;
  uint32_t i;

  val = sol->value;
  queue = sol->stack.lit;

  for (i = sol->stack.prop_ptr; i < sol->stack.top; i++) {
    l = not(queue[i]);
    
    bin = sol->bin[l];
    if (bin != NULL && ! propagation_via_bin_vector(sol, val, l, bin)) {
      return false; // conflict found
    }
    
    if (! propagation_via_watched_list(sol, val, sol->watch + l)) {
      return false;
    }
  }

  sol->stack.prop_ptr = i;

  return true;
}




/*******************************************************
 *  CONFLICT ANALYSIS AND CREATION OF LEARNED CLAUSES  *
 ******************************************************/

/*
 * Increase activity of variable x
 */
static void increase_var_activity(bit_solver_t *solver, bvar_t x) {
  int32_t i;
  var_heap_t *heap;

  heap = &solver->heap;
  if ((heap->activity[x] += heap->act_increment) > VAR_ACTIVITY_THRESHOLD) {
    rescale_var_activities(heap, solver->nvars);
  }

  // move x up if it's in the heap
  i = heap->heap_index[x];
  if (i >= 0) {
    update_up(heap, x, i);
  }
}



/*
 * Decision level for assigned literal l
 */
static inline uint32_t d_level(bit_solver_t *sol, literal_t l) {
  return sol->level[var_of(l)];
}

/*
 * Prepare to backtrack: search for a literal of second
 * highest decision level and set backtrack_level
 * - sol->buffer contains the learned clause, with UIP in sol->buffer.data[0]
 */
static void prepare_to_backtrack(bit_solver_t *sol) {
  uint32_t i, j, d, x, n;
  literal_t l, *b;

  b = sol->buffer.data;
  n = sol->buffer.size;

  if (n == 1) {
    sol->backtrack_level = sol->base_level;
    return;
  }

  d = sol->base_level; // make sure we never backtrack beyond that
  j = 0;
  for (i=1; i<n; i++) {
    x = d_level(sol, b[i]);
    if (x > d) { 
      d = x; 
      j = i;
    }
  }

  assert(j == 0 || d > sol->base_level);

  if (j > 1) {
    // swap b[1] and b[j]
    l = b[1]; b[1] = b[j]; b[j] = l;
  }

  // record backtrack level
  sol->backtrack_level = d;
}


/*
 * Check whether var_of(l) is unmarked
 */
static inline bool is_lit_unmarked(bit_solver_t *sol, literal_t l) {
  return ! tst_bit(sol->mark, var_of(l));
}

static inline bool is_lit_marked(bit_solver_t *sol, literal_t l) {
  return tst_bit(sol->mark, var_of(l));
}

/*
 * Set mark for literal l
 */
static inline void set_lit_mark(bit_solver_t *sol, literal_t l) {
  set_bit(sol->mark, var_of(l));
}

/*
 * Clear mark for literal l
 */
static inline void clear_lit_mark(bit_solver_t *sol, literal_t l) {
  clr_bit(sol->mark, var_of(l));
}


/*
 * Auxiliary function to accelerate clause simplification (cf. Minisat). 
 * This builds a hash of the decision levels in a literal array.
 * b = array of literals
 * n = number of literals
 */
static inline uint32_t signature(bit_solver_t *sol, literal_t *b, uint32_t n) {
  uint32_t i, s;

  s = 0;
  for (i=0; i<n; i++) {
    s |= 1 << (d_level(sol, b[i]) & 31);
  }
  return s;
}

/*
 * Check whether decision level for literal l matches the hash sgn
 */
static inline bool check_level(bit_solver_t *sol, literal_t l, uint32_t sgn) {
  return (sgn & (1 << (d_level(sol, l) & 31))) != 0;
}


/*
 * Analyze literal antecedents of l to check whether l is subsumed.
 * - sgn = signature of the learned clause
 * level of l must match sgn (i.e., check_level(sol, l, sgn) is not 0).
 * 
 * - returns false if l is not subsumed: either because l has no antecedent
 *   or if an antecedent of l has a decision level that does not match sgn.
 * - returns true otherwise.
 * Unmarked antecedents of l are marked and pushed into sol->buffer2
 */
static bool analyze_antecedents(bit_solver_t *sol, literal_t l, uint32_t sgn) {
  bvar_t x;
  antecedent_t a;
  literal_t l1;
  uint32_t i;
  ivector_t *b;
  literal_t *c;

  x = var_of(l);
  a = sol->antecedent[x];
  if (a == mk_literal_antecedent(null_literal)) {
    return false;
  }

  b = &sol->buffer2;
  switch (antecedent_tag(a)) {
  case clause0_tag:
  case clause1_tag:
    c = clause_antecedent(a)->cl;
    i = clause_index(a);
    // other watched literal
    assert(c[i] == not(l));
    l1 = c[i^1];
    if (is_lit_unmarked(sol, l1)) {
      set_lit_mark(sol, l1);
      ivector_push(b, l1);
    }
    // rest of the clause
    i = 2;
    l1 = c[i];
    while (l1 >= 0) {
      if (is_lit_unmarked(sol, l1)) {
	if (check_level(sol, l1, sgn)) {
	  set_lit_mark(sol, l1);
	  ivector_push(b, l1);
	} else {
	  return false;
	}
      }
      i ++;
      l1 = c[i];
    }
    break;

  case literal_tag:
    l1 = literal_antecedent(a);
    if (is_lit_unmarked(sol, l1)) {
      set_lit_mark(sol, l1);
      ivector_push(b, l1);
    }
    break;
    
  case generic_tag:
    assert(false);
  }

  return true;
}


/*
 * Check whether literal l is subsumed by other marked literals
 * - sgn = signature of the learned clause (in which l occurs)
 * The function uses sol->buffer2 as a queue
 */
static bool subsumed(bit_solver_t *sol, literal_t l, uint32_t sgn) {
  uint32_t i, n;
  ivector_t *b;

  b = &sol->buffer2;
  n = b->size;
  i = n;
  while (analyze_antecedents(sol, l, sgn)) {
    if (i < b->size) {
      l = b->data[i];
      i ++;
    } else {
      return true;
    }
  }

  // cleanup
  for (i=n; i<b->size; i++) {
    clear_lit_mark(sol, b->data[i]);
  }
  b->size = n;

  return false;
}


/*
 * Simplification of a learned clause
 * - the clause is stored in sol->buffer as an array of literals
 * - sol->buffer[0] is the UIP
 */
static void simplify_learned_clause(bit_solver_t *sol) {
  uint32_t hash;
  literal_t *b;
  literal_t l;
  uint32_t i, j, n;

  
  b = sol->buffer.data;
  n = sol->buffer.size;
  hash = signature(sol, b+1, n-1); // skip b[0]. It cannot subsume anything.

  assert(sol->buffer2.size == 0);

  // remove the subsumed literals
  j = 1;
  for (i=1; i<n; i++) {
    l = b[i];
    if (subsumed(sol, l, hash)) { 
      // Hack: move l to buffer2 to clear its mark later
      ivector_push(&sol->buffer2, l); 
    } else {
      // keep k in buffer
      b[j] = l;
      j ++;
    }
  }

  sol->stats.literals_before_simpl += n;
  sol->stats.subsumed_literals += n - j;
  sol->buffer.size = j;

  // remove the marks of literals in learned clause
  for (i=0; i<j; i++) {
    clear_lit_mark(sol, b[i]);
  }

  // remove the marks of subsumed literals
  b = sol->buffer2.data;
  n = sol->buffer2.size;
  for (i=0; i<n; i++) {
    clear_lit_mark(sol, b[i]);
  }

  ivector_reset(&sol->buffer2);
}




/*
 * Check whether var x is unmarked
 */
static inline bool is_var_unmarked(bit_solver_t *sol, bvar_t x) {
  return ! tst_bit(sol->mark, x);
}

static inline bool is_var_marked(bit_solver_t *sol, bvar_t x) {
  return tst_bit(sol->mark, x);
}

/*
 * Set mark for variable x
 */
static inline void set_var_mark(bit_solver_t *sol, bvar_t x) {
  set_bit(sol->mark, x);
}


/*
 * Clear mark for variable x
 */
static inline void clr_var_mark(bit_solver_t *sol, bvar_t x) {
  clr_bit(sol->mark, x);
}


/*
 * Search for first UIP and build the learned clause
 * sol = solver state
 *   sol->cl stores a conflict clause (i.e., an array of literals 
 *   terminated by -1 with all literals in sol->cl false).
 * result:
 * - the learned clause is stored in sol->buffer as an array of literals
 * - sol->buffer.data[0] is the UIP
 */
#define process_literal(l)                    \
do {                                          \
  x = var_of(l);                              \
  if (is_var_unmarked(sol, x)) {              \
    set_var_mark(sol, x);                     \
    increase_var_activity(sol, x);            \
    if (sol->level[x] < conflict_level) {     \
      ivector_push(buffer, l);                \
    } else {                                  \
      unresolved ++;                          \
    }                                         \
  }                                           \
} while(0)


static void analyze_conflict(bit_solver_t *sol) {
  uint32_t i, j, conflict_level, unresolved;
  literal_t l, b;
  bvar_t x;
  literal_t *c,  *stack;
  antecedent_t a;
  clause_t *cl;
  ivector_t *buffer;

  conflict_level = sol->decision_level;
  assert(conflict_level > sol->base_level);

  buffer = &sol->buffer;
  unresolved = 0;

  // reserve space for the UIP literal
  ivector_reset(buffer);
  ivector_push(buffer, null_literal); 

  /*
   * scan the conflict clause
   * - all literals of dl < conflict_level are added to buffer
   * - all literals are marked
   * - unresolved = number of literals in the conflict
   *   clause whose decision level is equal to conflict_level
   */
  c = sol->conflict;
  l = *c;
  while (l >= 0) {
    process_literal(l);
    c ++;
    l = *c;
  }

  /*
   * If the conflict is a learned clause, increase its activity
   */
  if (l == end_learned) {
    increase_clause_activity(sol, sol->false_clause);
  }

  /*
   * Scan the assignement stack from top to bottom and process the
   * antecedent of all marked literals.
   */
  stack = sol->stack.lit;
  j = sol->stack.top;
  for (;;) {
    j --;
    b = stack[j];
    if (is_lit_marked(sol, b)) {
      assert(sol->level[var_of(b)] == conflict_level);
      if (unresolved == 1) {
	// b is the UIP literal we're done.
	buffer->data[0] = not(b);
	break;

      } else {
	unresolved --;
	clear_lit_mark(sol, b);
	a = sol->antecedent[var_of(b)];
	/*
	 * Process b's antecedent:
	 */
	switch (antecedent_tag(a)) {
	case clause0_tag:
	case clause1_tag:
	  cl = clause_antecedent(a);
	  i = clause_index(a);
	  c = cl->cl;
	  assert(c[i] == b);
	  // process other watched literal
	  l = c[i^1];
	  process_literal(l);
	  // rest of the clause
	  c += 2;
	  l = *c;
	  while (l >= 0) {
	    process_literal(l);
	    c ++;
	    l = *c;
	  }
	  if (l == end_learned) {
	    increase_clause_activity(sol, cl);
	  }
	  break;

	case literal_tag:
	  l = literal_antecedent(a);
	  process_literal(l);
	  break;

	case generic_tag:
	  assert(false);
	}
      }
    }
  }

  /*
   * Simplify the learned clause and clear the marks
   */
  simplify_learned_clause(sol);

  /*
   * Find backtrack level
   * Move a literal of second highest decision level in position 1
   */
  prepare_to_backtrack(sol);
}





/*****************************
 *  MAIN SOLVING PROCEDURES  *
 ****************************/


/*
 * Select an unassigned literal l.
 * - returns null_literal (i.e., -1) if all literals are assigned.
 */
static literal_t select_literal(bit_solver_t *solver) {
  literal_t l;
  uint32_t rnd;
  bvar_t x;
  uint8_t *v;

  v = solver->value;

  rnd = random_uint32() & 0xFFFFFF;
  if (rnd <= (uint32_t) (0x1000000 * VAR_RANDOM_FACTOR)) {
    l = random_uint(solver->nlits);
    if (v[l] == VAL_UNDEF) {
      solver->stats.random_decisions ++;
      return l;
    }
  }

  /* 
   * select unassigned variable x with highest activity
   * return neg_lit(x) (same as minisat heuristic)
   * HACK: this works (and terminates) even if the heap is empty,
   * because neg_lit(-1) = -1 and v[-1] = VAL_UNDEF.
   */
  do {
    x = heap_get_top(&solver->heap);
    l = neg_lit(x);
  } while (v[l] != VAL_UNDEF);

  // if polarity[x] == 1 use pos_lit(x) rather than neg_lit[x]
  if (x >= 0 && tst_bit(solver->polarity, x)) {
    l = not(l);
  }
  
  return l;
}


/*
 * Backtrack to the given level
 * - undo all assignments done at levels >= back_level + 1
 * - requires sol->decision_level > back_level, otherwise
 *   level_index[back_level+1] may not be set properly
 */
static inline void backtrack(bit_solver_t *sol, uint32_t back_level) {
  uint32_t i;
  uint32_t d;
  literal_t *s, l;
  bvar_t x;

  assert(sol->base_level <= back_level && back_level < sol->decision_level);

  s = sol->stack.lit;
  d = sol->stack.level_index[back_level + 1];
  i = sol->stack.top;
  while (i > d) {
    i --;
    l = s[i];

    assert(sol->value[l] == VAL_TRUE);
    assert(sol->level[var_of(l)] > back_level || 
	   (sol->level[var_of(l)] == 0 && is_lit_marked(sol, l)));

    sol->value[l] = VAL_UNDEF;
    sol->value[not(l)] = VAL_UNDEF;

    x = var_of(l);
    heap_insert(&sol->heap, x);

    // save current polarity: 0 if l =neg_lit(x), 1 if l = pos_lit(x);
    assign_bit(sol->polarity, x, is_pos(l));
  }

  sol->stack.top = i;
  sol->stack.prop_ptr = i;
  sol->decision_level = back_level;
}


/*
 * Search until the given number of conflict is reached.
 * - sol: solver
 * - conflict_bound: number of conflict 
 * output: STATUS_SAT, STATUS_SEARCHING, or STATUS_UNSAT
 */
static smt_status_t bit_solver_search(bit_solver_t *sol, uint32_t conflict_bound) {
  literal_t l, *b;
  uint32_t nb_conflicts, n;
  clause_t *cl;

  sol->stats.restarts ++;
  nb_conflicts = 0;

  for (;;) {
    if (propagation(sol)) {
      /*
       * No conflict
       */
      if (nb_conflicts >= conflict_bound) {
      	if (sol->decision_level > sol->base_level) {
	  backtrack(sol, sol->base_level);
	}
      	return STATUS_SEARCHING;
      }

      // Simplify at the base level 
      //      if (sol->decision_level == sol->base_level &&
      if (sol->decision_level == sol->base_level &&
	  sol->stack.top > sol->simplify_bottom && 
	  sol->stats.propagations >= sol->simplify_props + sol->simplify_threshold) {
	simplify_clause_database(sol);
	sol->simplify_bottom = sol->stack.top;
	sol->simplify_props = sol->stats.propagations;
	sol->simplify_threshold = sol->stats.learned_literals + sol->stats.prob_literals + 2 * sol->nb_bin_clauses;
      }

      // Delete half the learned clauses if the threshold is reached
      // then increase the threshold
      if (get_cv_size(sol->learned_clauses) >= sol->reduce_threshold) {
	reduce_learned_clause_set(sol);
	sol->reduce_threshold = (uint32_t) (sol->reduce_threshold * REDUCE_FACTOR);
      }

      l = select_literal(sol);
      if (l == null_literal) {
	sol->status = STATUS_SAT;
	return STATUS_SAT;
      }
      // assign l to true
      bit_solver_decide_literal(sol, l);

    } else {
      /*
       * RESOLVE THE CONFLICT
       */
      sol->stats.conflicts ++;
      nb_conflicts ++;

      // Check if UNSAT
      if (sol->decision_level == sol->base_level) {
	sol->status = STATUS_UNSAT;
	return STATUS_UNSAT;
      }

      // Otherwise: deal with the conflict
      analyze_conflict(sol);

      backtrack(sol, sol->backtrack_level);
      b = sol->buffer.data;
      n = sol->buffer.size;
      l = b[0];

      assert(sol->value[l] == VAL_UNDEF);

      // Add the learned clause and set the implied literal (UIP)
      if (n >= 3) {
	cl = add_learned_clause(sol, n, b);
	implied_literal(sol, l, mk_clause0_antecedent(cl));

      } else if (n == 2) {
	bit_solver_add_binary_clause(sol, l, b[1]);
	implied_literal(sol, l, mk_literal_antecedent(b[1]));

      } else {
	assert(n == 1);
	assign_literal(sol, l);
      }

      decay_var_activities(&sol->heap);
      decay_clause_activities(sol);
    }
  }
}



/*
 * Start the search:
 * - base_level must be zero
 * - reset all counters
 * - perform one round of boolean propagation
 * - if there's no conflict, set status to SEARCHING,
 *   and return true.
 * - if there's a conflict, set status to UNSAT
 *   and return false
 */
bool bit_solver_start_search(bit_solver_t *solver) {
  bvar_t x;

  assert(solver->base_level == 0);

  // reset the counters
  solver->stats.restarts = 0;
  solver->stats.simplify_calls = 0;
  solver->stats.reduce_calls = 0;
  solver->stats.decisions = 0;
  solver->stats.random_decisions = 0;
  solver->stats.propagations = 0;
  solver->stats.conflicts = 0;

  // check for initial conflict
  if (solver->status == STATUS_UNSAT) return false;

  if (! propagation(solver)) {
    solver->status = STATUS_UNSAT;
    return false;
  }

  if (solver->nb_unit_clauses > 0) {
    simplify_clause_database(solver);
    solver->simplify_bottom = solver->stack.top;
  }

  // Initialize the heap
  for (x = 0; x < solver->nvars; x ++) {
    if (solver->value[pos_lit(x)] == VAL_UNDEF) {
      heap_insert(&solver->heap, x);
    }
  }

  solver->status = STATUS_SEARCHING;

  return true;
}



/*
 * Assign all the literals in the saved unit vector
 */
static void process_saved_units(bit_solver_t *solver) {
  ivector_t *v;
  uint32_t i, n;
  literal_t l;

  assert(solver->decision_level == solver->base_level);

  v = &solver->saved_units;
  n = v->size;
  for (i=0; i<n; i++) {
    l = v->data[i];
    assert(is_lit_marked(solver, l));

    switch (solver->value[l]) {
    case VAL_TRUE: // already assigned
      assert(solver->level[var_of(l)] == 0);
      break;

    case VAL_UNDEF:
      solver->value[l] = VAL_TRUE;
      solver->value[not(l)] = VAL_FALSE;
      push_literal(&solver->stack, l);
      solver->level[var_of(l)] = 0;
      solver->antecedent[var_of(l)] = mk_literal_antecedent(null_literal);
      break;

    case VAL_FALSE:
    default:
      assert(false);
      break;
    }
  }

  // empty saved units if we're at level 0
  if (solver->base_level == 0) {
    ivector_reset(v);
  }  
}


/*
 * Add l as an assumption
 * - return false if that causes a conflict, true otherwise
 */
bool bit_solver_assume(bit_solver_t *solver, literal_t l) {
  assert(solver->status == STATUS_SEARCHING && 
	 solver->base_level == solver->decision_level);

  ivector_push(&solver->assumptions, l);

  /* 
   * First make sure all literals in delayed unit clauses are 
   * assigned properly.
   */
  process_saved_units(solver);

  switch (solver->value[l]) {
  case VAL_FALSE:
    // immediate contradiction: other assumptions imply (\not l)
    // store l as the conflict clause
    solver->conflict_buffer[0] = l;
    solver->conflict_buffer[1] = end_clause;
    solver->conflict = solver->conflict_buffer;
    solver->status = STATUS_UNSAT;
    return false;

  case VAL_UNDEF:
    // push l onto the assigment stack
    // increment base_level and do one round of propagation
    bit_solver_decide_literal(solver, l);
    solver->base_level ++;
    if (! propagation(solver)) {
      solver->status = STATUS_UNSAT;
      return false;
    }
    break;

  case VAL_TRUE:
    // redundant assumption
    ivector_push(&solver->redundant_assumptions, l);
    break;
  }

  return true;
}



/*
 * Check whether l is the last element of vector v
 */
static inline bool is_last_elem(literal_t l, ivector_t *v) {
  return v->size > 0 && l == ivector_last(v);
}



/*
 * Apply resolution to the clause c (array of literals terminated by -1 or -2)
 * - trace back the implications until only assumption
 *   literals are left.
 * - add all these assumption literals in v
 */
static void bit_solver_get_assumptions(bit_solver_t *solver, literal_t *c, ivector_t *v) {
  literal_t *stack;
  clause_t *cl;
  antecedent_t a;
  literal_t l, b;
  bvar_t x;
  uint32_t j, unresolved;

  /*
   * resolution: for each l in c
   * - mark l
   * - unresolved = number of literals marked
   */
  l = *c;
  unresolved = 0;  
  do {
    assert(l >= 0 && solver->value[l] == VAL_FALSE);
    x = var_of(l);
    // x is marked iff l is true at level 0
    if (is_var_unmarked(solver, x)) {
      set_var_mark(solver, x);
      unresolved ++;
    }
    c ++;
    l = *c;
  } while (l >= 0);


  /*
   * Scan the assignment stack from top to bottom and resolve
   * all the marked literals.
   */
  stack = solver->stack.lit;
  j = solver->stack.top;
  while (unresolved > 0) {
    j --;
    b = stack[j];
    x = var_of(b);

    /*
     * If x is marked and has level 0, then { b } is a unit clause
     * so it can't be an assumption. Otherwise, if x is marked it's
     * then b is one of the unresolved literals.
     */
    if (is_var_marked(solver, x) && solver->level[x] > 0) {
      // resolve the antecedent clause of b
      unresolved --;
      clr_var_mark(solver, x);
      a = solver->antecedent[x];
      
      switch (antecedent_tag(a)) {
      case clause0_tag:
      case clause1_tag:
	cl = clause_antecedent(a);
	c = cl->cl;
	l = *c;
	do {
	  assert(l >= 0);
	  if (l != b) {
	    assert(solver->value[l] == VAL_FALSE);
	    if (is_lit_unmarked(solver, l)) {
	      set_lit_mark(solver, l);
	      unresolved ++;
	    }
	  }
	  c ++;
	  l = *c;
	} while (l >= 0);
	break;

      case literal_tag:
	l = literal_antecedent(a);
	if (l == null_literal) {
	  // b is an assumption: add it to vector v
	  ivector_push(v, b);
	} else if (is_lit_unmarked(solver, l)) {
	  // mark l to be resolved
	  set_lit_mark(solver, l);
	  unresolved ++;
	}
	break;

      case generic_tag:
	assert(false);
      }
    }

  }
}


/*
 * Compute the unsat core
 * - store a (minimal?) set of inconsistent assumptions in v
 */
void bit_solver_get_unsat_core(bit_solver_t *solver, ivector_t *v) {
  literal_t *c;
  literal_t l;

  assert(solver->status == STATUS_UNSAT && 
	 solver->base_level == solver->decision_level);

  c = solver->conflict;
  l = *c;
  // if l is the last assumption, then it must be added to v
  if (is_last_elem(l, &solver->assumptions)) {
    ivector_push(v, l);
  }

  // compute the antecedents of the conflict clause
  bit_solver_get_assumptions(solver, c, v);
}



/*
 * Compute an explanation (in terms of the assumed literals)
 * for a literal l
 * - l must be true in the current assignment
 */
void bit_solver_explain_literal(bit_solver_t *solver, literal_t l, ivector_t *v) {
  literal_t aux[2];

  assert(0 <= l && l < solver->nlits && solver->value[l] == VAL_TRUE);
  aux[0] = not(l);
  aux[1] = end_clause;

  bit_solver_get_assumptions(solver, aux, v);
}



/*
 * Remove the last assumption l and reset status to SEARCHING
 * - if l is false, there's nothing to do: it was a contradictory assumption
 * - if l is true, we undo all assignments implied by l (unless l was 
 *   redundant).
 */
void bit_solver_retract(bit_solver_t *solver) {
  literal_t l;

  assert(solver->base_level == solver->decision_level);

  l = ivector_last(&solver->assumptions);
  ivector_pop(&solver->assumptions);
  assert(solver->value[l] == VAL_FALSE || solver->value[l] == VAL_TRUE);

  if (solver->value[l] == VAL_TRUE) {
    if (is_last_elem(l, &solver->redundant_assumptions)) {
      // l is a redundant assumption, just remove it
      ivector_pop(&solver->redundant_assumptions);
    } else {
      /*
       * We need to backtrack to the level before l was assumed
       */
      assert(solver->level[var_of(l)] == solver->base_level && solver->base_level > 0);      
      solver->base_level --;
      backtrack(solver, solver->base_level);
    }
  }

  solver->status = STATUS_SEARCHING;
}



/*
 * Remove all assumptions
 */
void bit_solver_retract_all(bit_solver_t *solver) {
  assert(solver->base_level == solver->decision_level);

  ivector_reset(&solver->assumptions);
  ivector_reset(&solver->redundant_assumptions);
  
  if (solver->base_level > 0) {
    backtrack(solver, 0);
    solver->base_level = 0;
    solver->status = STATUS_SEARCHING;
  }
}




/*
 * Solve procedure
 */
smt_status_t bit_solver_check(bit_solver_t *sol) {
  smt_status_t code;
  uint32_t c_threshold, d_threshold;

  assert(sol->status == STATUS_SEARCHING);

#if TRACE
  // reset some counters (they are used only if trace is enabled)
  sol->stats.decisions = 0;
  sol->stats.random_decisions = 0;
#endif

  /*
   * restart strategy based on picosat/luby
   */
  // c_threshold = number of conflicts in each iteration
  // increased by RETART_FACTOR after each iteration
  c_threshold = INITIAL_RESTART_THRESHOLD;
  d_threshold = INITIAL_RESTART_THRESHOLD;

  // initial reduce threshold
  sol->reduce_threshold = sol->nb_clauses/4;
  if (sol->reduce_threshold < MIN_REDUCE_THRESHOLD) {
    sol->reduce_threshold = MIN_REDUCE_THRESHOLD;
  }

#if TRACE
  printf("\n"
	 "  Bit solver check: %"PRIu32" assumptions, %"PRIu32" variables\n"
	 "                            Unit    Binary   Problem   Learned   Learned    Decisions\n"
	 "           C         D   Clauses   Clauses   Clauses   Clauses     Lits.\n",
	 bit_solver_num_assumptions(sol), bit_solver_nvars(sol));
#endif

  do {
#if TRACE
    printf("    %8"PRIu32"  %8"PRIu32"  %8"PRIu32"  %8"PRIu32"  %8"PRIu32"  %8"PRIu32"  %8"PRIu64"     %8"PRIu64"\n",
	   c_threshold, d_threshold, sol->nb_unit_clauses, sol->nb_bin_clauses, sol->nb_prob_clauses, 
	   get_cv_size(sol->learned_clauses), sol->stats.learned_literals, sol->stats.decisions);
    fflush(stdout);
#endif

    code = bit_solver_search(sol, c_threshold);
   
    c_threshold = (uint32_t)(c_threshold * RESTART_FACTOR_C);  // multiply by 1.1
    if (c_threshold > d_threshold) {
      c_threshold = INITIAL_RESTART_THRESHOLD;
      d_threshold = (uint32_t)(d_threshold * RESTART_FACTOR_D);
      if (d_threshold > MAX_DTHRESHOLD) {
	d_threshold = MAX_DTHRESHOLD;
      }
    }
 
  } while (code == STATUS_SEARCHING);

#if TRACE
  if (code == STATUS_UNSAT) {
    printf("  Bit solver done: conflict (%"PRIu64" decisions)\n", sol->stats.decisions);
  } else {
    printf("  Bit solver done: no conflict (%"PRIu64" decisions)\n", sol->stats.decisions);
  }
  fflush(stdout);
#endif

  return code;
}




/*
 * Return the model: copy all variable value into val
 */
void get_allvars_assignment(bit_solver_t *solver, bval_t *val) {
  uint32_t i, n;

  n = solver->nvars;
  for (i=0; i<n; i++) {
    val[i] = solver->value[pos_lit(i)];
  }
}


/*
 * Copy all true literals in array a:
 * - a must have size >= solver->nvars.
 * return the number of literals added to a.
 *
 * If solver->status == sat this should be equal to solver->nvars.
 */
uint32_t get_true_literals(bit_solver_t *solver, literal_t *a) {
  uint32_t n;
  literal_t l;

  n = 0;
  for (l = 0; l<solver->nlits; l++) {
    if (solver->value[l] == VAL_TRUE) {
      a[n] = l;
      n ++;
    }
  }

  return n;
}



/*
 * Cleanup after check
 */
void bit_solver_restore(bit_solver_t *solver) {
  if (solver->decision_level > solver->base_level) {
    backtrack(solver, solver->base_level);
  }

  restore_clause_database(solver);
  solver->status = STATUS_SEARCHING;
}


/*
 * Reset
 * - backtrack to level 0
 * - reset status to IDLE
 */
void bit_solver_clear(bit_solver_t *solver) {
  if (solver->decision_level > 0) {
    backtrack(solver, 0);
  }
  solver->status = STATUS_IDLE;
}
