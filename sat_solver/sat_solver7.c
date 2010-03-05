/*
 * Baseline SAT solver (Version 7)
 * - same data structures as version 1
 * - restart strategy similar to Minisat
 * - negative branching
 * - lower clause-deletion threshold and threshold increased only
 *   after a restart
 *
 * Mostly based on Minisat but with different data structures.
 */

#include <assert.h>
#include <stddef.h>
#include <float.h>

#include <stdio.h>
#include <inttypes.h>

#include "memalloc.h"
#include "int_array_sort.h"
#include "prng.h"

#include "./sat_solver7.h"
#include "./parameters.h"

#define DEBUG 0
#define TRACE 0


/*
 * Internal checks
 */
#if DEBUG

static void check_literal_vector(literal_t *v);
static void check_propagation(sat_solver_t *sol);
static void check_marks(sat_solver_t *sol);
static void check_top_var(sat_solver_t *sol, bvar_t x);

#endif





/*
 * CLAUSES AND LEARNED CLAUSES
 */

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
 * Mark a clause cl for deletion
 */
static inline void mark_for_deletion(clause_t *cl) {
  cl->cl[0] = cl->cl[1];
}

/*
 * Check whether the clause is to be deleted
 */
static inline bool is_clause_to_be_deleted(clause_t *cl) {
  return cl->cl[0] == cl->cl[1];
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
 * Header of vector v
 */
static inline clause_vector_t *cv_header(clause_t **v) {
  return (clause_vector_t *)(((char *)v) - offsetof(clause_vector_t, data));
}

static inline uint32_t get_cv_size(clause_t **v) {
  return cv_header(v)->size;
}

static inline void set_cv_size(clause_t **v, uint32_t sz) {
  cv_header(v)->size = sz;
}

static inline uint32_t get_cv_capacity(clause_t **v) {
  return cv_header(v)->capacity;
}


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
 * Size and capacity of a literal vector v
 */
static inline literal_vector_t *lv_header(literal_t *v) {
  return (literal_vector_t *)(((char *) v) - offsetof(literal_vector_t, data));
}

static inline uint32_t get_lv_size(literal_t *v) {
  return lv_header(v)->size;
}

static inline void set_lv_size(literal_t *v, uint32_t sz) {
  lv_header(v)->size = sz;
}

static inline uint32_t get_lv_capacity(literal_t *v) {
  return lv_header(v)->capacity;
}


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
static void delete_literal_vector(literal_t *v) {
  if (v != NULL) {
    safe_free(lv_header(v));
  }
}










/***********
 *  STACK  *
 **********/

/*
 * Initialize stack s for nvar
 */
static void init_stack(sol_stack_t *s, uint32_t nvar) {
  s->lit = (literal_t *) safe_malloc(nvar * sizeof(literal_t));
  s->level_index = (uint32_t *) safe_malloc(DEFAULT_NLEVELS * sizeof(uint32_t));
  s->level_index[0] = 0;
  s->top = 0;
  s->prop_ptr = 0;
  s->nlevels = DEFAULT_NLEVELS;
}

/*
 * Extend the size: nvar = new size
 */
static void extend_stack(sol_stack_t *s, uint32_t nvar) {
  s->lit = (literal_t *) safe_realloc(s->lit, nvar * sizeof(literal_t));
}

/*
 * Extend the level_index array by 50%
 */
static void increase_stack_levels(sol_stack_t *s) {
  uint32_t n;

  n = s->nlevels;
  n += n>>1;
  s->level_index = (uint32_t *) safe_realloc(s->level_index, n * sizeof(uint32_t));
  s->nlevels = n;
}

/*
 * Free memory used by stack s 
 */
static void delete_stack(sol_stack_t *s) {
  free(s->lit);
  free(s->level_index);
}

/*
 * Push literal l on top of stack s
 */
static inline void push_literal(sol_stack_t *s, literal_t l) {
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
 * i = current position of x in the heap (or heap_size if x is being inserted)
 */
static void update_up(var_heap_t *heap, bvar_t x, uint32_t i) {
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
 * Remove root of the heap (i.e., heap->heap[1]):
 * - move the variable currently in heap->heap[last] 
 *   into a new position.
 * - decrement last.
 */
static void update_down(var_heap_t *heap) {
  double ax, *act;
  int32_t* index;
  bvar_t *h, x, y;
  uint32_t i, j, last;

  h = heap->heap;
  index = heap->heap_index;
  act = heap->activity;
  last = heap->heap_last;

  if (last <= 1 ) { // empty heap.
    heap->heap_last = 0;
    return; 
  }

  heap->heap_last = last - 1;

  ax = act[h[last]]; // activity of last heap element.
 
  i = 1;      // root  
  j = 2;      // left child of i
  
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
 * - returns null_var (i.e., -1) if the heap is empty.
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
  update_down(heap);

  return top;
}

/*
 * Rescale variable activities: divide by VAR_ACTIVITY_THRESHOLD
 * \param heap = pointer to a heap structure
 * \param n = number of variables
 */
static void rescale_var_activities(var_heap_t *heap) {
  uint32_t i, n;
  double *act;

  n = heap->size;
  act = heap->activity;
  for (i=0; i<n; i++) {
    act[i] *= INV_VAR_ACTIVITY_THRESHOLD;
  }
  heap->act_increment *= INV_VAR_ACTIVITY_THRESHOLD;
}


/*
 * Increase activity of variable x
 */
static void increase_var_activity(var_heap_t *heap, bvar_t x) {
  int32_t i;

  if ((heap->activity[x] += heap->act_increment) > VAR_ACTIVITY_THRESHOLD) {
    rescale_var_activities(heap);
  }

  // move x up if it's in the heap
  i = heap->heap_index[x];
  if (i >= 0) {
    update_up(heap, x, i);
  }
}


/*
 * Decay
 */
static inline void decay_var_activities(var_heap_t *heap) {
  heap->act_increment *= heap->inv_act_decay;
}


/******************************************
 *  SOLVER ALLOCATION AND INITIALIZATION  *
 *****************************************/

/*
 * Initialize a statistics record
 */
static void init_stats(solver_stats_t *stat) {
  stat->starts = 0;
  stat->simplify_calls = 0;
  stat->reduce_calls = 0;
  stat->remove_calls = 0;
  stat->decisions = 0;
  stat->random_decisions = 0;
  stat->propagations = 0;
  stat->conflicts = 0;
  stat->prob_literals = 0;
  stat->learned_literals = 0;
  stat->aux_literals = 0;
  stat->prob_clauses_deleted = 0;
  stat->learned_clauses_deleted = 0;
  stat->bin_clauses_deleted = 0;
  stat->literals_before_simpl = 0;
  stat->subsumed_literals = 0;
}

/*
 * Allocate and initialize a solver
 * size = initial size fo the variable arrays
 */
void init_sat_solver(sat_solver_t *solver, uint32_t size) {
  uint32_t lsize;

  if (size >= MAX_VARIABLES) {
    out_of_memory();
  }

  lsize = size + size;
  solver->status = status_unsolved;
  solver->nb_vars = 0;
  solver->nb_lits = 0;
  solver->vsize = size;
  solver->lsize = lsize;

  solver->nb_clauses = 0;
  solver->nb_unit_clauses = 0;
  solver->nb_bin_clauses = 0;

  solver->cla_inc = INIT_CLAUSE_ACTIVITY_INCREMENT;
  solver->inv_cla_decay = 1/CLAUSE_DECAY_FACTOR;

  solver->decision_level = 0;
  solver->backtrack_level = 0;

  solver->simplify_bottom = 0;
  solver->simplify_props = 0;
  solver->simplify_threshold = 0;

  init_stats(&solver->stats);

  // Clause database
  solver->problem_clauses = new_clause_vector(DEF_CLAUSE_VECTOR_SIZE);
  solver->learned_clauses = new_clause_vector(DEF_CLAUSE_VECTOR_SIZE);

  // Variable-indexed arrays: not initialized
  solver->antecedent = (antecedent_t *) safe_malloc(size * sizeof(antecedent_t)); 
  solver->level = (uint32_t *) safe_malloc(size * sizeof(uint32_t));
  solver->mark = allocate_bitvector(size);
  solver->polarity = allocate_bitvector(size);

  // Literal-indexed arrays
  // value is indexed from -2 to 2n -1, with value[-2] = value[-1] = VAL_UNDEF
  solver->value = (uint8_t *) safe_malloc((lsize + 2) * sizeof(uint8_t)) + 2;
  solver->value[-2] = val_undef; // for end_learned marker
  solver->value[-1] = val_undef; // for end_clause marker
  solver->bin = (literal_t **) safe_malloc(lsize * sizeof(literal_t *));
  solver->watch = (link_t *) safe_malloc(lsize * sizeof(link_t));

  // Heap
  init_heap(&solver->heap, size);

  // Stack
  init_stack(&solver->stack, size);

  // Auxiliary buffer
  init_ivector(&solver->buffer, DEF_LITERAL_BUFFER_SIZE);
  init_ivector(&solver->buffer2, DEF_LITERAL_BUFFER_SIZE);

  // solver->short_buffer not initialized but that's fine.
  solver->conflict = NULL;
  solver->false_clause = NULL;
}


/*
 * Free memory
 */
void delete_sat_solver(sat_solver_t *solver) {
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

  
  // var-indexed arrays
  safe_free(solver->antecedent);
  safe_free(solver->level);
  delete_bitvector(solver->mark);
  delete_bitvector(solver->polarity);

  // literal values
  safe_free(solver->value - 2);

  // delete the literal vectors in the propagation structures
  n = solver->nb_lits;
  for (i=0; i<n; i++) {
    delete_literal_vector(solver->bin[i]);
  }
  safe_free(solver->bin);
  safe_free(solver->watch);

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
static void sat_solver_extend(sat_solver_t *solver, uint32_t new_size) {
  uint32_t lsize;
  uint8_t *tmp;

  if (new_size >= MAX_VARIABLES) {
    out_of_memory();
  }

  lsize = new_size + new_size;
  solver->vsize = new_size;
  solver->lsize = lsize;

  solver->antecedent = (antecedent_t *) safe_realloc(solver->antecedent, new_size * sizeof(antecedent_t));
  solver->level = (uint32_t *) safe_realloc(solver->level, new_size * sizeof(uint32_t));
  solver->mark = extend_bitvector(solver->mark, new_size);
  solver->polarity = extend_bitvector(solver->polarity, new_size);

  tmp = solver->value - 2;
  tmp = (uint8_t *) safe_realloc(tmp, (lsize + 2) * sizeof(uint8_t));
  solver->value = tmp + 2;
  solver->bin = (literal_t **) safe_realloc(solver->bin, lsize * sizeof(literal_t *));
  solver->watch = (link_t *) safe_realloc(solver->watch, lsize * sizeof(link_t));

  extend_heap(&solver->heap, new_size);
  extend_stack(&solver->stack, new_size);
}


/*
 * Add n variables
 */
void sat_solver_add_vars(sat_solver_t *solver, uint32_t n) {
  uint32_t nvars, new_size, i;
  literal_t l0, l1;

  nvars = solver->nb_vars;
  if (nvars + n > solver->vsize) {
    new_size = solver->vsize + 1;
    new_size += new_size >> 1;
    if (new_size < nvars + n) {
      new_size = nvars + n;
    }
    sat_solver_extend(solver, new_size);
    assert(nvars + n <= solver->vsize);
  }

  for (i=nvars; i<nvars+n; i++) {
    clr_bit(solver->mark, i);
    clr_bit(solver->polarity, i);  // 0 means negative
    solver->level[i] = UINT32_MAX;
    solver->antecedent[i] = mk_literal_antecedent(null_literal);
    l0 = pos_lit(i);
    l1 = neg_lit(i);
    solver->value[l0] = val_undef;
    solver->value[l1] = val_undef;
    solver->bin[l0] = NULL;
    solver->bin[l1] = NULL;
    solver->watch[l0] = NULL_LINK;
    solver->watch[l1] = NULL_LINK;
  }

  solver->nb_vars += n;
  solver->nb_lits += 2 * n;
}



/*
 * Allocate and return a fresh boolean variable
 */
bvar_t sat_solver_new_var(sat_solver_t *solver) {
  uint32_t new_size, i;
  literal_t l0, l1;

  i = solver->nb_vars;
  if (i >= solver->vsize) {
    new_size = solver->vsize + 1;
    new_size += new_size >> 1;
    sat_solver_extend(solver, new_size);
    assert(i < solver->vsize);
  }

  clr_bit(solver->mark, i);
  clr_bit(solver->polarity, i);
  solver->level[i] = UINT32_MAX;
  solver->antecedent[i] = mk_literal_antecedent(null_literal);
  l0 = pos_lit(i);
  l1 = neg_lit(i);
  solver->value[l0] = val_undef;
  solver->value[l1] = val_undef;
  solver->bin[l0] = NULL;
  solver->bin[l1] = NULL;
  solver->watch[l0] = NULL_LINK;
  solver->watch[l1] = NULL_LINK;

  solver->nb_vars ++;
  solver->nb_lits += 2;

  return i;
}



/*
 * Assign literal l at base level
 */
static void assign_literal(sat_solver_t *solver, literal_t l) {
  bvar_t v;

#if TRACE
  printf("---> Assigning literal %d, decision level = %u\n", l, solver->decision_level);
#endif
  assert(0 <= l && l < solver->nb_lits);
  assert(solver->value[l] == val_undef);
  assert(solver->decision_level == 0);

  solver->value[l] = val_true;
  solver->value[not(l)] = val_false;
  push_literal(&solver->stack, l);

  v = var_of(l);
  solver->level[v] = 0;
  solver->antecedent[v] = mk_literal_antecedent(null_literal);
  set_bit(solver->mark, v); // marked at level 0
}


/*
 * Add empty clause: mark the whole thing as unsat
 */
void add_empty_clause(sat_solver_t *solver) {
  solver->status = status_unsat;
}

/*
 * Add unit clause { l }: push l on the assignment stack
 * or set status to unsat if l is already false
 */
void add_unit_clause(sat_solver_t *solver, literal_t l) {
#if TRACE
  printf("---> Add unit clause: { %d }\n", l);
#endif

  assert(0 <= l && l < solver->nb_lits);
  switch (solver->value[l]) {
  case val_false:
    solver->status = status_unsat;
    break;
  case val_undef:
    assign_literal(solver, l);
    solver->nb_unit_clauses ++;
    break;
  default: // val_true: nothing to do
    break;
  }
}

/*
 * Add clause { l0, l1 }
 */
void add_binary_clause(sat_solver_t *solver, literal_t l0, literal_t l1) {
#if TRACE
  printf("---> Add binary clause: { %d %d }\n", l0, l1);
#endif

  assert(0 <= l0 && l0 < solver->nb_lits);
  assert(0 <= l1 && l1 < solver->nb_lits);

  add_literal_to_vector(solver->bin + l0, l1);
  add_literal_to_vector(solver->bin + l1, l0);

  solver->nb_bin_clauses ++;
}

/*
 * Add an n-literal clause when n >= 3
 */
static void add_clause_core(sat_solver_t *solver, uint32_t n, literal_t *lit) {
  clause_t *cl;
  literal_t l;

#ifndef NDEBUG
  // check that all literals are valid
  uint32_t i;

  for (i=0; i<n; i++) {
    assert(0 <= lit[i] && lit[i] < solver->nb_lits);
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
  solver->nb_clauses ++;
  solver->stats.prob_literals += n;
}

/*
 * Add three-literal clause {l0, l1, l2} 
 */
void add_ternary_clause(sat_solver_t *solver, literal_t l0, literal_t l1, literal_t l2) {
  literal_t lit[3];

  lit[0] = l0;
  lit[1] = l1;
  lit[2] = l2;
  add_clause_core(solver, 3, lit);
}


/*
 * Add a clause of n literals
 */
void add_clause(sat_solver_t *solver, uint32_t n, literal_t *lit) {
  if (n > 2) {
    add_clause_core(solver, n, lit);
  } else if (n == 2) {
    add_binary_clause(solver, lit[0], lit[1]);
  } else if (n == 1) {
    add_unit_clause(solver, lit[0]);
  } else {
    add_empty_clause(solver);
  }
}



/*
 * More careful version: simplify a clause and add it to solver. 
 * No effect if sol is already unsat.
 */
void simplify_and_add_clause(sat_solver_t *solver, uint32_t n, literal_t *lit) {
  uint32_t i, j;
  literal_t l, l_aux;

  if (solver->status == status_unsat) return;

  if (n == 0) {
    add_empty_clause(solver);
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
    case val_false:
      break;
    case val_undef:
      lit[j] = l;
      j++;
      break;
    default: // true literal, so the clause is true
      return;
    }
  }
  n = j; // new clause size

  add_clause(solver, n, lit);
}



/**********************************
 *  ADDITION OF LEARNED CLAUSES   *
 *********************************/

/*
 * Rescale activity of all the learned clauses
 * (divide all by CLAUSE_ACTIVITY_THRESHOLD)
 */
static void rescale_clause_activities(sat_solver_t *solver) {
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
static inline void increase_clause_activity(sat_solver_t *solver, clause_t *cl) {
  increase_activity(cl, solver->cla_inc);
  if (get_activity(cl) > CLAUSE_ACTIVITY_THRESHOLD) {
    rescale_clause_activities(solver);
  }
}


/*
 * Decay
 */
static inline void decay_clause_activities(sat_solver_t *solver) {
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
static clause_t *add_learned_clause(sat_solver_t *solver, uint32_t n, literal_t *lit) {
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
    if (! is_clause_to_be_deleted(cl)) {
      *list = lnk;
      list = cdr_ptr(lnk);
    }
  }
  *list = NULL_LINK; // end of list
}


/*
 * Update all watch lists: remove all clauses marked for deletion.
 */
static void cleanup_watch_lists(sat_solver_t *solver) {
  uint32_t i, n;

  n = solver->nb_lits;
  for (i=0; i<n; i ++) {
    cleanup_watch_list(solver->watch + i);
  }
}


/*
 * Check whether cl is an antecedent clause
 */
static inline bool clause_is_locked(sat_solver_t *solver, clause_t *cl) {
  literal_t l0, l1;

  l0 = get_first_watch(cl);
  l1 = get_second_watch(cl);
  
  return (solver->value[l0] != val_undef && 
	  solver->antecedent[var_of(l0)] == mk_clause0_antecedent(cl))
    || (solver->value[l1] != val_undef && 
	solver->antecedent[var_of(l1)] == mk_clause1_antecedent(cl));
}


/*
 * Delete all clauses that are marked for deletion
 */
static void delete_learned_clauses(sat_solver_t *solver) {
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
    if (is_clause_to_be_deleted(v[i])) {
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
static void reduce_learned_clause_set(sat_solver_t *solver) {
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
      mark_for_deletion(v[i]);
    }
  }
  for (i = n/2; i<n; i++) {
    if (! clause_is_locked(solver, v[i])) {
      mark_for_deletion(v[i]);
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
 */
static void simplify_clause(sat_solver_t *solver, clause_t *cl) {
  uint32_t i, j;
  literal_t l;

  i = 0;
  j = 0;
  do {
    l = cl->cl[i];
    i ++;
    switch (solver->value[l]) {
      //    case val_false:
      //      break;

    case val_undef:
      cl->cl[j] = l;
      j ++;
      break;

    case val_true:
      mark_for_deletion(cl);
      return;
    }
  } while (l >= 0);

  solver->stats.aux_literals += j - 1;
  // could migrate cl to two-literal if j is 3??
}


/*
 * Simplify the set of clauses given the current assignment:
 * - remove all clauses that are true.
 * - remove false literals from clauses
 * DANGER: this is sound only if done at level 0.
 */
static void simplify_clause_set(sat_solver_t *solver) {
  uint32_t i, j, n;
  clause_t **v;

  // simplify problem clauses
  solver->stats.aux_literals = 0;
  v = solver->problem_clauses;
  n = get_cv_size(v);
  for (i=0; i<n; i++) simplify_clause(solver, v[i]);
  solver->stats.prob_literals = solver->stats.aux_literals;

  // simplify learned clauses
  solver->stats.aux_literals = 0;
  v = solver->learned_clauses;
  n = get_cv_size(v);
  for (i=0; i<n; i++) simplify_clause(solver, v[i]);
  solver->stats.learned_literals = solver->stats.aux_literals;

  // cleanup the watched literal lists
  cleanup_watch_lists(solver);

  // remove simplified problem clauses
  v = solver->problem_clauses;
  n = get_cv_size(v);
  j = 0;
  for (i=0; i<n; i++) {
    if (is_clause_to_be_deleted(v[i])) {
      delete_clause(v[i]);
    } else {
      v[j] = v[i];
      j ++;
    }
  }
  set_cv_size(v, j);
  solver->nb_clauses -= n - j;
  solver->stats.prob_clauses_deleted += n - j;

  // remove simplified learned clauses
  v = solver->learned_clauses;
  n = get_cv_size(v);
  j = 0;
  for (i=0; i<n; i++) {
    if (is_clause_to_be_deleted(v[i])) {
      delete_learned_clause(v[i]);
    } else {
      v[j] = v[i];
      j ++;
    }
  }
  set_cv_size(v, j);
  solver->nb_clauses -= n - j;
  solver->stats.learned_clauses_deleted += n - j;

  shrink_clause_vector(&solver->problem_clauses);
}


/*
 * Clean up a binary-clause vector v
 * - assumes that v is non-null
 * - remove all literals of v that are assigned
 * - for each deleted literal, increment sol->stats.aux_literals.
 */
static void cleanup_binary_clause_vector(sat_solver_t *solver, literal_t *v) {
  uint32_t i, j;
  literal_t l;

  i = 0;
  j = 0;
  do {
    l = v[i++];
    if (solver->value[l] == val_undef) { //keep l
      v[j ++] = l;
    }    
  } while (l >= 0); // end-marker is copied too

  solver->stats.aux_literals += i - j;
  set_lv_size(v, j - 1);
}


/*
 * Simplify all binary vectors affected by the current assignment
 * - scan the literals in the stack from sol->simplify_bottom to sol->stack.top
 * - remove all the binary clauses that contain one such literal
 * - free the binary watch vectors
 */
static void simplify_binary_vectors(sat_solver_t *solver) {
  uint32_t i, j, n;
  literal_t l0, *v0, l1;

  solver->stats.aux_literals = 0;   // counts the number of literals removed
  for (i = solver->simplify_bottom; i < solver->stack.top; i++) {
    l0 = solver->stack.lit[i];

    // remove all binary clauses that contain l0
    v0 = solver->bin[l0];
    if (v0 != NULL) {
      n = get_lv_size(v0);
      for (j=0; j<n; j++) {
	l1 = v0[j];
	if (solver->value[l1] == val_undef) {
	  // sol->bin[l1] is non null.
	  assert(solver->bin[l1] != NULL);
	  cleanup_binary_clause_vector(solver, solver->bin[l1]);
	}
      }

      delete_literal_vector(v0);
      solver->bin[l0] = NULL;
      solver->stats.aux_literals += n;
    }

    // remove all binary clauses that contain not(l0)
    l0 = not(l0);
    v0 = solver->bin[l0];
    if (v0 != NULL) {
      solver->stats.aux_literals += get_lv_size(v0);
      delete_literal_vector(v0);
      solver->bin[l0] = NULL;
    }
  }

  solver->stats.aux_literals /= 2;
  solver->stats.bin_clauses_deleted += solver->stats.aux_literals;
  solver->nb_bin_clauses -= solver->stats.aux_literals;

  solver->stats.aux_literals = 0;
}


/*
 * Simplify all the database: problem clauses, learned clauses,
 * and binary clauses.
 *
 * UNSOUND UNLESS DONE AT DECISION-LEVEL 0 AND AFTER ALL
 * PROPAGATIONS HAVE BEEN PERFORMED.
 */
static void simplify_clause_database(sat_solver_t *solver) {
  assert(solver->decision_level == 0);
  assert(solver->stack.top == solver->stack.prop_ptr);

  solver->stats.simplify_calls ++;
  simplify_clause_set(solver);
  simplify_binary_vectors(solver);
}



/*************************
 *  LITERAL ASSIGNMENT   *
 ***********************/

/*
 * Decide literal: increase decision level then
 * assign literal l to true and push it on the stack
 */
static void decide_literal(sat_solver_t *solver, literal_t l) {
  uint32_t d;
  bvar_t v;

  assert(solver->value[l] == val_undef);

  solver->stats.decisions ++;

  // Increase decision level
  d = solver->decision_level + 1;
  solver->decision_level = d;
  if (solver->stack.nlevels <= d) {
    increase_stack_levels(&solver->stack);
  }
  solver->stack.level_index[d] = solver->stack.top;

  solver->value[l] = val_true;
  solver->value[not(l)] = val_false;
  push_literal(&solver->stack, l);

  v = var_of(l);
  solver->level[v] = d;
  solver->antecedent[v] = mk_literal_antecedent(null_literal);

#if TRACE
  printf("---> Decision: literal %d, decision level = %u\n", l, solver->decision_level);
#endif
}


/*
 * Assign literal l to true and attach antecedent a.
 * solver->mark[v] is set if decision level = 0
 */
static void implied_literal(sat_solver_t *solver, literal_t l, antecedent_t a) {
  bvar_t v;

  assert(solver->value[l] == val_undef);

#if TRACE
  printf("---> Implied literal %d, decision level = %u\n", l, solver->decision_level);
#endif

  solver->stats.propagations ++;

  solver->value[l] = val_true;
  solver->value[not(l)] = val_false;
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
 *   store literals in short_buffer, add terminator -1, and
 *   record a pointer to short_buffer.
 */

/*
 * Record a two-literal conflict: clause {l0, l1} is false
 */
static inline void record_binary_conflict(sat_solver_t *solver, literal_t l0, literal_t l1) {
#if TRACE
  printf("\n---> Binary conflict: {%d, %d}\n", l0, l1);
#endif

  solver->short_buffer[0] = l0;
  solver->short_buffer[1] = l1; 
  solver->short_buffer[2] = end_clause;
  solver->conflict = solver->short_buffer;
}


/*
 * Record cl as a conflict clause
 */
static inline void record_clause_conflict(sat_solver_t *solver, clause_t *cl) {
#if TRACE
  uint32_t i;
  literal_t ll;

  printf("\n---> Conflict: {%d, %d", get_first_watch(cl), get_second_watch(cl));
  i = 2;
  ll = cl->cl[i];
  while (ll >= 0) {
    printf(", %d", ll);
    i++;
    ll = cl->cl[i];
  }
  printf("}\n");
#endif

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
 * Code returned is either no_conflict or binary_conflict
 */
static int32_t propagation_via_bin_vector(sat_solver_t *sol, uint8_t *val, literal_t l0, literal_t *v) {
  literal_t l1;
  bval_t v1;

  assert(v != NULL);
  assert(sol->value == val && sol->bin[l0] == v && sol->value[l0] == val_false);

  for (;;) {
    // Search for non-true literals in v
    // This terminates since val[end_marker] = VAL_UNDEF
    do {
      l1 = *v ++;
      v1 = val[l1];
    } while (v1 == val_true);

    if (l1 < 0) break; // end_marker

    if (v1 == val_undef) {
      implied_literal(sol, l1, mk_literal_antecedent(l0));
    } else {
      record_binary_conflict(sol, l0, l1);
      return binary_conflict;
    }
  }

  return no_conflict;
}


/*
 * Propagation via the watched lists of a literal l0.
 * - sol = solver
 * - val = literal value array (must be sol->value)
 * - list = start of the watch list (must be sol->watch + l0)
 */
static inline int propagation_via_watched_list(sat_solver_t *sol, uint8_t *val, link_t *list) {
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

    if (v1 == val_true) {
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
       * and val[end_marker] == val_undef.
       */
      k = 1;
      b = cl->cl;
      do {
	k ++;
	l = b[k];
      } while (val[l] == val_false);
      
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
	if (v1 == val_undef) {
	  // l1 is implied
	  implied_literal(sol, l1, mk_clause_antecedent(cl, i^1));

	  // move to the next clause
	  *list = link;
	  list = cl->link + i;
	  link = cl->link[i];

	} else {
	  // v1 == val_false: conflict found
	  record_clause_conflict(sol, cl);
	  *list = link;
	  return clause_conflict;
	}
      }
    }
  }

  *list = NULL_LINK;

  return no_conflict;
}


/*
 * Full propagation: until either the propagation queue is empty,
 * or a conflict is found
 *
 * Variant: do propagation via only the binary vectors before a 
 * full propagation via the watched lists. (2007/07/07)
 * Variant gave bad experimental results. Reverted to previous method.
 */
static int32_t propagation(sat_solver_t *sol) {
  uint8_t *val;
  literal_t *queue;
  literal_t l, *bin;
  // uint32_t i, j;
  uint32_t i;
  int32_t code;

  val = sol->value;
  queue = sol->stack.lit;

#if 0
  i = sol->stack.prop_ptr;
  j = i;
  for (;;) {
    if (i < sol->stack.top) {
      l = not(queue[i]);
      i ++;
      bin = sol->bin[l];
      if (bin != NULL) {
	code = propagation_via_bin_vector(sol, val, l, bin);
  	if (code != no_conflict) return code;
      }
    } else if (j < sol->stack.top) {
      l = not(queue[j]);
      j ++;
      code = propagation_via_watched_list(sol, val, sol->watch + l);
      if (code != no_conflict) return code;
    } else {
      break;
    }
  }
#endif

  for (i = sol->stack.prop_ptr; i < sol->stack.top; i++) {
    l = not(queue[i]);
    
    bin = sol->bin[l];
    if (bin != NULL) {
      code = propagation_via_bin_vector(sol, val, l, bin);
      if (code != no_conflict) return code;
    }
    
    code = propagation_via_watched_list(sol, val, sol->watch + l);
    if (code != no_conflict) return code;
  }

  sol->stack.prop_ptr = i;
  return no_conflict;
}




/*******************************************************
 *  CONFLICT ANALYSIS AND CREATION OF LEARNED CLAUSES  *
 ******************************************************/

/*
 * Decision level for assigned literal l
 */
static inline uint32_t d_level(sat_solver_t *sol, literal_t l) {
  return sol->level[var_of(l)];
}

/*
 * Prepare to backtrack: search for a literal of second
 * highest decision level and set backtrack_level
 * - sol->buffer contains the learned clause, with UIP in sol->buffer.data[0]
 */
static void prepare_to_backtrack(sat_solver_t *sol) {
  uint32_t i, j, d, x, n;
  literal_t l, *b;

  b = sol->buffer.data;
  n = sol->buffer.size;

  if (n == 1) {
    sol->backtrack_level = 0;
    return;
  }

  j = 1;
  l = b[1];
  d = d_level(sol, l);
  for (i=2; i<n; i++) {
    x = d_level(sol, b[i]);
    if (x > d) { 
      d = x; 
      j = i; 
    }
  }

  // swap b[1] and b[j]
  b[1] = b[j];
  b[j] = l;

  // record backtrack level
  sol->backtrack_level = d;
}


/*
 * Check whether var_of(l) is unmarked
 */
static inline bool is_lit_unmarked(sat_solver_t *sol, literal_t l) {
  return tst_bit(sol->mark, var_of(l)) == 0;
}

static inline bool is_lit_marked(sat_solver_t *sol, literal_t l) {
  return tst_bit(sol->mark, var_of(l)) != 0;
}

/*
 * Set mark for literal l
 */
static inline void set_lit_mark(sat_solver_t *sol, literal_t l) {
  set_bit(sol->mark, var_of(l));
}

/*
 * Clear mark for literal l
 */
static inline void clear_lit_mark(sat_solver_t *sol, literal_t l) {
  clr_bit(sol->mark, var_of(l));
}


/*
 * Auxiliary function to accelerate clause simplification (cf. Minisat). 
 * This builds a hash of the decision levels in a literal array.
 * b = array of literals
 * n = number of literals
 */
static inline uint32_t signature(sat_solver_t *sol, literal_t *b, uint32_t n) {
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
static inline bool check_level(sat_solver_t *sol, literal_t l, uint32_t sgn) {
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
static bool analyze_antecedents(sat_solver_t *sol, literal_t l, uint32_t sgn) {
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
static bool subsumed(sat_solver_t *sol, literal_t l, uint32_t sgn) {
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
static void simplify_learned_clause(sat_solver_t *sol) {
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
static inline bool is_var_unmarked(sat_solver_t *sol, bvar_t x) {
  return tst_bit(sol->mark, x) == 0;
}

static inline bool is_var_marked(sat_solver_t *sol, bvar_t x) {
  return tst_bit(sol->mark, x) != 0;
}

/*
 * Set mark for literal l
 */
static inline void set_var_mark(sat_solver_t *sol, bvar_t x) {
  set_bit(sol->mark, x);
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
    increase_var_activity(&sol->heap, x);     \
    if (sol->level[x] < conflict_level) {     \
      ivector_push(buffer, l);                \
    } else {                                  \
      unresolved ++;                          \
    }                                         \
  }                                           \
} while(0)


static void analyze_conflict(sat_solver_t *sol) {
  uint32_t i, j, conflict_level, unresolved;
  literal_t l, b;
  bvar_t x;
  literal_t *c,  *stack;
  antecedent_t a;
  clause_t *cl;
  ivector_t *buffer;

  conflict_level = sol->decision_level;
  buffer = &sol->buffer;
  unresolved = 0;

#if DEBUG
  check_marks(sol);
#endif

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
      if (unresolved == 1) {
	// b is the UIP literal we're done.
	assert(sol->level[var_of(b)] == conflict_level);
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

#if DEBUG
  check_marks(sol);
#endif

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
static literal_t select_literal(sat_solver_t *solver) {
  literal_t l;
  uint32_t rnd;
  bvar_t x;
  uint8_t *v;

  v = solver->value;

  rnd = random_uint32() & 0xFFFFFF;
  if (rnd <= (uint32_t) (0x1000000 * VAR_RANDOM_FACTOR)) {
    //if (drand() < VAR_RANDOM_FACTOR) {
    //    select l at random between 0 and nb_lits-1
    //    l = irand(solver->nb_lits);
    l = random_uint(solver->nb_lits);
    if (v[l] == val_undef) {
#if TRACE
      printf("---> Random selection: literal %d\n", l);
#endif
      solver->stats.random_decisions ++;
      return l;
    }
  }

  /* 
   * select unassigned variable x with highest activity
   * return neg_lit(x) (same as minisat heuristic)
   * HACK: this works (and terminates) even if the heap is empty,
   * because neg_lit(-1) = -1 and v[-1] = val_undef.
   */
  do {
    x = heap_get_top(&solver->heap);
    l = neg_lit(x);
  } while (v[l] != val_undef);

#if DEBUG
  check_top_var(solver, x);
#endif

  return l;
}


/*
 * Backtrack to the given level
 * - undo all assignments done at levels >= back_level + 1
 * - requires sol->decision_level > back_level, otherwise
 *   level_index[back_level+1] may not be set properly
 */
static inline void backtrack(sat_solver_t *sol, uint32_t back_level) {
  uint32_t i;
  uint32_t d;
  literal_t *s, l;
  bvar_t x;

#if TRACE
  printf("---> Backtracking to level %u\n", back_level);
#endif

  assert(back_level < sol->decision_level);

  s = sol->stack.lit;
  d = sol->stack.level_index[back_level + 1];
  i = sol->stack.top;
  while (i > d) {
    i --;
    l = s[i];

    assert(sol->value[l] == val_true);
    assert(sol->level[var_of(l)] > back_level);

    sol->value[l] = val_undef;
    sol->value[not(l)] = val_undef;

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
 * output: status_sat, status_unsolved, or status_unsat
 */
solver_status_t sat_search(sat_solver_t *sol, uint32_t conflict_bound) {
  int32_t code;
  literal_t l, *b;
  uint32_t nb_conflicts, n;
  clause_t *cl;

  sol->stats.starts ++;
  nb_conflicts = 0;

  for (;;) {
    code = propagation(sol);

    if (code == no_conflict) {
#if DEBUG
      check_propagation(sol);
#endif

      if (nb_conflicts >= conflict_bound) {
      	if (sol->decision_level > 0) {
	  backtrack(sol, 0);
	}
      	return status_unsolved;
      }

      // Simplify at level 0
      if (sol->decision_level == 0 &&
	  sol->stack.top > sol->simplify_bottom && 
	  sol->stats.propagations >= sol->simplify_props + sol->simplify_threshold) {
#if TRACE
	printf("---> Simplify\n");
	printf("---> level = %u, bottom = %u, top = %u\n", sol->decision_level, sol->simplify_bottom, sol->stack.top);
	printf("---> props = %"PRIu64", threshold = %"PRIu64"\n", sol->stats.propagations, sol->simplify_threshold);
#endif
	simplify_clause_database(sol);
	sol->simplify_bottom = sol->stack.top;
	sol->simplify_props = sol->stats.propagations;
	sol->simplify_threshold = sol->stats.learned_literals + sol->stats.prob_literals + 2 * sol->nb_bin_clauses;
      }

      // Delete half the learned clauses if the threshold is reached
      if (get_cv_size(sol->learned_clauses) >= sol->reduce_threshold) {
	reduce_learned_clause_set(sol);
	//	sol->reduce_threshold = (uint32_t) (sol->reduce_threshold * REDUCE_FACTOR);
      }

      l = select_literal(sol);
      if (l == null_literal) {
	sol->status = status_sat;
	return status_sat;
      }
      // assign l to true
      decide_literal(sol, l);

    } else {      
      sol->stats.conflicts ++;
      nb_conflicts ++;

      // Check if UNSAT or conflict bound reached
      if (sol->decision_level == 0) {
	sol->status = status_unsat;
	return status_unsat;
      }

      // Otherwise: deal with the conflict
      analyze_conflict(sol);

      backtrack(sol, sol->backtrack_level);
      b = sol->buffer.data;
      n = sol->buffer.size;
      l = b[0];

      // Add the learned clause and set the implied literal (UIP)
      if (n >= 3) {
	cl = add_learned_clause(sol, n, b);
	implied_literal(sol, l, mk_clause0_antecedent(cl));

      } else if (n == 2) {
	add_binary_clause(sol, l, b[1]);
	implied_literal(sol, l, mk_literal_antecedent(b[1]));

      } else {
	assert(n > 0);

	add_unit_clause(sol, l);
	if (sol->status == status_unsat) {
	  return status_unsat;
	}
      }

      decay_var_activities(&sol->heap);
      decay_clause_activities(sol);
    }
  }
}



/*
 * Solve procedure
 */
solver_status_t solve(sat_solver_t *sol) {
  int32_t code;
  bvar_t x;
  uint32_t c_threshold;

  if (sol->status == status_unsat) return status_unsat;

#if DEBUG
  uint32_t i;

  check_marks(sol);
  for (i=0; i<sol->nb_lits; i++) {
    check_literal_vector(sol->bin[i]);
  }
#endif

  code = propagation(sol);
  
  if (code != no_conflict) {
    sol->status = status_unsat;
    return status_unsat;
  }

#if DEBUG
  check_propagation(sol);
#endif

  if (sol->nb_unit_clauses > 0) {
    simplify_clause_database(sol);
    sol->simplify_bottom = sol->stack.top;
  }

  // Initialize the heap
  for (x = 0; x < sol->nb_vars; x ++) {
    if (sol->value[pos_lit(x)] == val_undef) {
      heap_insert(&sol->heap, x);
    }
  }

  /*
   * restart strategy based on Minisat
   */
  // c_threshold = number of conflicts in each iteration
  // increased by RETART_FACTOR after each iteration
  c_threshold = INITIAL_RESTART_THRESHOLD;

  // initial reduce threshold: 1/3 of initial number of clauses (like Minisat)
  sol->reduce_threshold = sol->nb_clauses/3;


  printf("---------------------------------------------------------------------------------\n");
  printf("|     Thresholds    |  Binary   |      Original     |          Learned          |\n");
  printf("|   Conf.      Del. |  Clauses  |   Clauses   Lits. |   Clauses  Lits. Lits/Cl. |\n");
  printf("---------------------------------------------------------------------------------\n");

  printf("| %7"PRIu32"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu64" | %8"PRIu32" %8"PRIu64" %7.1f |\n", 
	 c_threshold, sol->reduce_threshold, sol->nb_bin_clauses,
	 get_cv_size(sol->problem_clauses), sol->stats.prob_literals,
	 get_cv_size(sol->learned_clauses), sol->stats.learned_literals,
	 ((double) sol->stats.learned_literals)/get_cv_size(sol->learned_clauses));
  fflush(stdout);


  do {
#if DEBUG
    check_marks(sol);
#endif
    code = sat_search(sol, c_threshold);

#if DEBUG
    check_marks(sol);
#endif

    c_threshold = (uint32_t)(c_threshold * MINISAT_RESTART_FACTOR);  // multiply by 1.5
    sol->reduce_threshold = (uint32_t) (sol->reduce_threshold * MINISAT_REDUCE_FACTOR); // multiply by 1.1

    printf("| %7"PRIu32"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu64" | %8"PRIu32" %8"PRIu64" %7.1f |\n", 
	   c_threshold, sol->reduce_threshold, sol->nb_bin_clauses,
	   get_cv_size(sol->problem_clauses), sol->stats.prob_literals,
	   get_cv_size(sol->learned_clauses), sol->stats.learned_literals,
	   ((double) sol->stats.learned_literals)/get_cv_size(sol->learned_clauses));
    fflush(stdout);
 
  } while (code == status_unsolved);

  printf("---------------------------------------------------------------------------------\n");
  fflush(stdout);

  return code;
}




/*
 * Return the model: copy all variable value into val
 */
void get_allvars_assignment(sat_solver_t *solver, bval_t *val) {
  uint32_t i, n;

  n = solver->nb_vars;
  for (i=0; i<n; i++) {
    val[i] = solver->value[pos_lit(i)];
  }
}


/*
 * Copy all true literals in array a:
 * - a must have size >= solver->nb_vars.
 * return the number of literals added to a.
 *
 * If solver->status == sat this should be equal to solver->nb_vars.
 */
uint32_t get_true_literals(sat_solver_t *solver, literal_t *a) {
  uint32_t n;
  literal_t l;

  n = 0;
  for (l = 0; l<solver->nb_lits; l++) {
    if (solver->value[l] == val_true) {
      a[n] = l;
      n ++;
    }
  }

  return n;
}





/***************
 *  DEBUGGING  *
 **************/

#if DEBUG

/*
 * Check whether all variables in the heap have activity <= x
 */
static void check_top_var(sat_solver_t *solver, bvar_t x) {
  uint32_t i, n;
  bvar_t y;
  var_heap_t *heap;
  
  heap = &solver->heap;
  n = heap->heap_last;
  for (i=1; i<n; i++) {
    y = heap->heap[i];
    if (solver->value[y] == val_undef && heap->activity[y] > heap->activity[x]) {
      printf("ERROR: incorrect heap\n");
      fflush(stdout);
    }
  }
}

/*
 * Check literal vector
 */
static void check_literal_vector(literal_t *v) {
  uint32_t i, n;

  if (v != NULL) {
    n = get_lv_size(v);
    i = get_lv_capacity(v);
    if (n > i - 1) {
      printf("ERROR: overflow in literal vector %p: size = %u, capacity = %u\n",
	     v, n, i);
    } else {
      for (i=0; i<n; i++) {
	if (v[i] < 0) {
	  printf("ERROR: negative literal %d in vector %p at index %u (size = %u)\n", 
		 v[i], v, i, n);
	}	
      }
      if (v[i] != null_literal) {
	printf("ERROR: missing terminator in vector %p (size = %u)\n", v, n);
      }
    }
  }
}

/*
 * Check propagation results
 */
static void check_propagation_bin(sat_solver_t *sol, literal_t l0) {
  literal_t l1, *v;
  uint8_t *val;

  v = sol->bin[l0];
  val = sol->value;
  if (v == NULL || val[l0] != val_false) return;

  l1 = *v ++;
  while (l1 >= 0) {
    if (val[l1] == val_undef) {
      printf("ERROR: missed propagation. Binary clause {%d, %d}\n", l0, l1);
    } else if (val[l1] == val_false) {
      printf("ERROR: missed conflict. Binary clause {%d, %d}\n", l0, l1);
    }
    l1 = *v ++;
  }
}

static inline int32_t indicator(bval_t v, bval_t c) {
  return (v == c) ? 1 : 0;
}

static void check_watch_list(sat_solver_t *sol, literal_t l, clause_t *cl) {
  link_t lnk;

  for (lnk = sol->watch[l]; lnk != NULL_LINK; lnk = next_of(lnk)) {
    if (clause_of(lnk) == cl) {
      return;
    }
  }

  printf("ERROR: missing watch, literal = %d, clause = %p\n", l, clause_of(lnk));
}


static void check_propagation_clause(sat_solver_t *sol, clause_t *cl) {
  literal_t l0, l1, l;
  literal_t *d;
  uint8_t *val;
  int32_t nf, nt, nu;
  uint32_t i;

  nf = 0;
  nt = 0;
  nu = 0;
  val = sol->value;

  l0 = get_first_watch(cl);
  nf += indicator(val[l0], val_false);
  nt += indicator(val[l0], val_true);
  nu += indicator(val[l0], val_undef);

  l1 = get_second_watch(cl);
  nf += indicator(val[l1], val_false);
  nt += indicator(val[l1], val_true);
  nu += indicator(val[l1], val_undef);

  d = cl->cl;
  i = 2;
  l = d[i];
  while (l >= 0) {
    nf += indicator(val[l], val_false);
    nt += indicator(val[l], val_true);
    nu += indicator(val[l], val_undef);

    i ++;
    l = d[i];
  }

  if (nt == 0 && nu == 0) {
    printf("ERROR: missed conflict. Clause {%d, %d", l0, l1);
    i = 2;
    l = d[i];
    while (l >= 0) {
      printf(", %d", l);
      i ++;
      l = d[i];
    }
    printf("} (addr = %p)\n", cl);
  }

  if (nt == 0 && nu == 1) {
    printf("ERROR: missed propagation. Clause {%d, %d", l0, l1);
    i = 2;
    l = d[i];
    while (l >= 0) {
      printf(", %d", l);
      i ++;
      l = d[i];
    }
    printf("} (addr = %p)\n", cl);
  }

  check_watch_list(sol, l0, cl);
  check_watch_list(sol, l1, cl);
}

static void check_propagation(sat_solver_t *sol) {
  literal_t l0;
  uint32_t i, n;
  clause_t **v;

  for (l0=0; l0<sol->nb_lits; l0++) {
    check_propagation_bin(sol, l0);
  }

  v = sol->problem_clauses;
  n = get_cv_size(v);
  for (i=0; i<n; i++) check_propagation_clause(sol, v[i]);

  v = sol->learned_clauses;
  n = get_cv_size(v);
  for (i=0; i<n; i++) check_propagation_clause(sol, v[i]);
}



/*
 * Check that marks/levels and assignments are consistent
 */
static void check_marks(sat_solver_t *sol) {
  uint32_t i, n;
  bvar_t x;
  literal_t l;

  for (x=0; x<sol->nb_vars; x++) {
    if (is_var_marked(sol, x) && sol->level[x] != 0) {
      printf("Warning: var %d marked but level[%d] = %u\n", x, x, sol->level[x]);
      fflush(stdout);
    }
  }

  n = sol->nb_unit_clauses;
  for (i=0; i<n; i++) {
    l = sol->stack.lit[i];
    if (is_lit_unmarked(sol, l)) {
      printf("Warning: literal %d assigned at level %d but not marked\n", 
	     l, d_level(sol, l));
      fflush(stdout);
    }
  }
}


#endif
