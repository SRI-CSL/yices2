/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Baseline SAT solver
 *
 * Mostly based on Minisat but with different data structures.
 */

#include <assert.h>
#include <stddef.h>
#include <float.h>
#include <stdio.h>
#include <inttypes.h>

#include "solvers/cdcl/sat_parameters.h"
#include "solvers/cdcl/sat_solver.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"
#include "utils/prng.h"

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
 * - i must be 0 or 1
 */
static inline literal_t get_other_watch(clause_t *cl, uint32_t i) {
  // flip low-order bit of i
  return cl->cl[1 - i];
}

/*
 * Get pointer to learned_clause in which clause cl is embedded.
 */
static inline learned_clause_t *learned(const clause_t *cl) {
  return (learned_clause_t *)(((char *)cl) - offsetof(learned_clause_t, clause));
}

/*
 * Activity of a learned clause
 */
static inline float get_activity(const clause_t *cl) {
  return learned(cl)->activity;
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



/*
 * Ordering function for clause deletion:
 * - c1 and c2 are two learned clauses
 * - the function must return true if we prefer to keep c2
 *   rather than c1 (i.e., c1's score is worse than c2's score).
 */
static bool clause_cmp(const void *aux, const void *c1, const void *c2) {
  return get_activity(c1) <= get_activity(c2);
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

#if DEBUG
#endif

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
static void push_literal(sol_stack_t *s, literal_t l) {
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
 * - we also use -2 as a marker with negative activity
 * - activity increment and threshold are set to their
 *   default initial value.
 */
static void init_heap(var_heap_t *heap, uint32_t n) {
  uint32_t i;
  double *tmp;

  tmp = (double *) safe_malloc((n+2) * sizeof(double));
  heap->activity = tmp + 2;
  heap->heap_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  heap->heap = (bvar_t *) safe_malloc((n+1) * sizeof(bvar_t));

  for (i=0; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }

  heap->activity[-2] = -1.0;
  heap->activity[-1] = DBL_MAX;
  heap->heap[0] = -1;

  heap->heap_last = 0;
  heap->size = n;
  heap->vmax = 0;

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
  tmp = heap->activity - 2;
  tmp = (double *) safe_realloc(tmp, (n+2) * sizeof(double));
  heap->activity = tmp + 2;
  heap->heap_index = (int32_t *) safe_realloc(heap->heap_index, n * sizeof(int32_t));
  heap->heap = (int32_t *) safe_realloc(heap->heap, (n+1) * sizeof(int32_t));
  heap->size = n;

  for (i=old_size; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }
}

/*
 * Free the heap
 */
static void delete_heap(var_heap_t *heap) {
  safe_free(heap->activity - 2);
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

  for (;;) {
    j = i >> 1;    // parent of i
    y = h[j];      // variable at position j in the heap

    // The loop terminates since act[h[0]] = DBL_MAX
    if (act[y] >= ax) break;

    // move y down, into position i
    h[i] = y;
    index[y] = i;

    // move i up
    i = j;
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
  double *act;
  int32_t *index;
  bvar_t *h;
  bvar_t x, y, z;
  double ax, ay, az;
  uint32_t i, j, last;

  last = heap->heap_last;
  heap->heap_last = last - 1;
  if (last <= 1 ) { // empty heap.
    assert(heap->heap_last == 0);
    return;
  }

  h = heap->heap;
  index = heap->heap_index;
  act = heap->activity;

  z = h[last];   // last element
  h[last] = -2;  // set end marker: act[-2] is negative
  az = act[z];   // activity of the last element

  i = 1;      // root
  j = 2;      // left child of i
  while (j < last) {
    /*
     * find child of i with highest activity.
     * Since h[last] = -2, we don't check j+1 < last
     */
    x = h[j];
    y = h[j+1];
    ax = act[x];
    ay = act[y];
    if (ay > ax) {
      j++;
      x = y;
      ax = ay;
    }

    // x = child of node i of highest activity
    // j = position of x in the heap (j = 2i or j = 2i+1)
    if (az >= ax) break;

    // move x up, into heap[i]
    h[i] = x;
    index[x] = i;

    // go down one step.
    i = j;
    j <<= 1;
  }

  h[i] = z;
  index[z] = i;
}



/*
 * Insert x into the heap, using its current activity.
 * No effect if x is already in the heap.
 * - x must be between 0 and nvars - 1
 */
static void heap_insert(var_heap_t *heap, bvar_t x) {
  if (heap->heap_index[x] < 0) {
    // x not in the heap
    heap->heap_last ++;
    update_up(heap, x, heap->heap_last);
  }
}


/*
 * Check whether the heap is empty
 */
static inline bool heap_is_empty(var_heap_t *heap) {
  return heap->heap_last == 0;
}


/*
 * Get and remove top element
 * - the heap must not be empty
 */
static bvar_t heap_get_top(var_heap_t *heap) {
  bvar_t top;

  assert(heap->heap_last > 0);

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


/*
 * Cleanup the heap: remove variables until the top var is unassigned
 * or until the heap is empty
 */
static void cleanup_heap(sat_solver_t *sol) {
  var_heap_t *heap;
  bvar_t x;

  heap = &sol->heap;
  while (! heap_is_empty(heap)) {
    x = heap->heap[1];
    if (var_is_unassigned(sol, x)) {
      break;
    }
    assert(x >= 0 && heap->heap_last > 0);
    heap->heap_index[x] = -1;
    update_down(heap);
  }
}




/***********************************
 *  STATISTICS ON LEARNED CLAUSES  *
 **********************************/

#if INSTRUMENT_CLAUSES

/*
 * Global statistics record
 */
static learned_clauses_stats_t stat_buffer = {
  NULL, 0, 0, NULL,
};

#define SBUFFER_SIZE 20000


/*
 * Level map for computing glue
 */
static tag_map_t lvl;


/*
 * Initialize the buffer
 */
void init_learned_clauses_stats(FILE *f) {
  stat_buffer.data = (lcstat_t *) safe_malloc(SBUFFER_SIZE * sizeof(lcstat_t));
  stat_buffer.nrecords = 0;
  stat_buffer.size = SBUFFER_SIZE;
  stat_buffer.file = f;
  init_tag_map(&lvl, 100);
}


/*
 * Flush the buffer: save all in the file then reset nrecords to 0
 */
static void flush_stat_buffer(void) {
  FILE *f;
  lcstat_t *d;
  uint32_t i, n;

  d = stat_buffer.data;
  f = stat_buffer.file;
  n = stat_buffer.nrecords;
  for (i=0; i<n; i++) {
    fprintf(f, "%"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32" %"PRIu32"\n",
	    d->creation, d->last_prop, d->last_reso, d->deletion, d->props, d->resos,
	    d->base_glue, d->min_glue, d->glue);
    d ++;
  }
  fflush(f);
  stat_buffer.nrecords = 0;
}


/*
 * Add r to the buffer
 */
static void stat_buffer_push(lcstat_t *r) {
  uint32_t i;

  if (stat_buffer.data != NULL) {
    i = stat_buffer.nrecords;
    if (i == stat_buffer.size) {
      flush_stat_buffer();
      i = 0;
    }
    assert(i < stat_buffer.size);
    stat_buffer.data[i] = *r;
    stat_buffer.nrecords = i+1;
  }
}


/*
 * Save all statistics into the statistics file
 */
void flush_learned_clauses_stats(void) {
  if (stat_buffer.data != NULL) {
    flush_stat_buffer();
    safe_free(stat_buffer.data);
    stat_buffer.data = NULL;
    delete_tag_map(&lvl);
  }
}


/*
 * Compute the glue score of clause cl
 * If cl is {l1, ... l_n} then the glue score is the number
 * of distinct levels in level[l1], ...., level[l_n].
 *
 * NOTE: we use solver->level[var_of(l)] even if l is not currently
 * assigned. Since level[x] is not reset when we backtrack,
 * it keeps the last decision level at which x was assigned.
 */
static uint32_t glue_score(sat_solver_t *solver, clause_t *cl) {
  literal_t *a;
  literal_t l;
  uint32_t k, n;

  a = cl->cl;
  n = 0;
  for (;;) {
    l = *a ++;
    if (l < 0) break;
    k = solver->level[var_of(l)];
    if (tag_map_read(&lvl, k) == 0) {
      // level k not seen before
      tag_map_write(&lvl, k, 1);
      n ++;
    }
  }

  clear_tag_map(&lvl);

  return n;
}

/*
 * Initialize a learned clause statistics
 * - n = number of conflicts acts as the clause id
 * - we also set last_prop and last_reso to n to ensure that
 *   creation <= last_prop and creation <= last_reso
 */
static void learned_clause_created(sat_solver_t *solver, clause_t *cl) {
  learned_clause_t *tmp;
  uint32_t n;

  n = solver->stats.conflicts;

  tmp = learned(cl);
  tmp->stat.creation = n;
  tmp->stat.deletion = 0;
  tmp->stat.props = 0;
  tmp->stat.last_prop = n;
  tmp->stat.resos = 0;
  tmp->stat.last_reso = n;

  n = glue_score(solver, cl);

  tmp->stat.base_glue = n;
  tmp->stat.glue = n;
  tmp->stat.min_glue = n;
}


/*
 * Update the resolution statistics
 */
static void learned_clause_reso(sat_solver_t *solver, clause_t *cl) {
  learned_clause_t *tmp;

  tmp = learned(cl);
  tmp->stat.resos ++;
  tmp->stat.last_reso = solver->stats.conflicts;
}


/*
 * Update the propagation statistics
 */
static void learned_clause_prop(sat_solver_t *solver, clause_t *cl) {
  learned_clause_t *tmp;

  tmp = learned(cl);
  tmp->stat.props ++;
  tmp->stat.last_prop = solver->stats.conflicts;
}


/*
 * Deletion: update glue then record statistics
 */
static void learned_clause_deletion(sat_solver_t *solver, clause_t *cl) {
  learned_clause_t *tmp;
  uint32_t n;

  tmp = learned(cl);
  tmp->stat.deletion = solver->stats.conflicts;
  n = glue_score(solver, cl);
  tmp->stat.glue = n;
  if (tmp->stat.min_glue > n) {
    tmp->stat.min_glue = n;
  }
  stat_buffer_push(&tmp->stat);

  // reset the props and reso counters
  tmp->stat.props = 0;
  tmp->stat.resos = 0;
}


/*
 * Snapshot: collect data about the current set of learned clauses
 * then export that.
 * - HACK: we call learned_clause_deletion.
 */
static void snapshot(sat_solver_t *solver) {
  clause_t **cl;
  uint32_t i, n;

  cl = solver->learned_clauses;
  n = get_cv_size(cl);
  for (i=0; i<n; i++) {
    learned_clause_deletion(solver, cl[i]);
  }
  flush_stat_buffer();
}


#endif


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
 * size = initial size of the variable arrays
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

  // Literal-indexed arrays
  // value is indexed from -2 to 2n -1, with value[-2] = value[-1] = val_undef_false
  solver->value = (uint8_t *) safe_malloc((lsize + 2) * sizeof(uint8_t)) + 2;
  solver->value[-2] = val_undef_false;
  solver->value[-1] = val_undef_false;
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

  // Sorting object for clause deletion
  init_stable_sorter(&solver->sorter, NULL, clause_cmp);
}


/*
 * Set the prng seed
 */
void sat_solver_set_seed(sat_solver_t *solver, uint32_t s) {
  random_seed(s);
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
#if INSTRUMENT_CLAUSES
    learned_clause_deletion(solver, cl[i]);
#endif
    delete_learned_clause(cl[i]);
  }
  delete_clause_vector(cl);


  // var-indexed arrays
  safe_free(solver->antecedent);
  safe_free(solver->level);
  delete_bitvector(solver->mark);

  // delete the literal vectors in the propagation structures
  safe_free(solver->value - 2);
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

  delete_stable_sorter(&solver->sorter);
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

  if (nvars + n < nvars) {
    // arithmetic overflow: too many variables
    out_of_memory();
  }

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

    solver->level[i] = UINT32_MAX;
    solver->antecedent[i] = mk_literal_antecedent(null_literal);
    l0 = pos_lit(i);
    l1 = neg_lit(i);

    // preferred polarity = false
    solver->value[l0] = val_undef_false;
    solver->value[l1] = val_undef_true;

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

  solver->level[i] = UINT32_MAX;
  solver->antecedent[i] = mk_literal_antecedent(null_literal);
  l0 = pos_lit(i);
  l1 = neg_lit(i);

  // preferred polarity = false
  solver->value[l0] = val_undef_false;
  solver->value[l1] = val_undef_true;

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

  assert(! lit_is_assigned(solver, l));
  assert(solver->decision_level == 0);

  push_literal(&solver->stack, l);

  solver->value[l] = val_true;
  solver->value[not(l)] = val_false;

  v = var_of(not(l));
  solver->level[v] = 0;
  solver->antecedent[v] = mk_literal_antecedent(null_literal);
  set_bit(solver->mark, v); // marked at level 0
}


/*
 * Add empty clause: mark the whole thing as unsat
 */
void sat_solver_add_empty_clause(sat_solver_t *solver) {
  solver->status = status_unsat;
}

/*
 * Add unit clause { l }: push l on the assignment stack
 * or set status to unsat if l is already false
 */
void sat_solver_add_unit_clause(sat_solver_t *solver, literal_t l) {
#if TRACE
  printf("---> Add unit clause: { %d }\n", l);
#endif

  assert(0 <= l && l < solver->nb_lits);

  switch (lit_val(solver, l)) {
  case val_false:
    solver->status = status_unsat;
    break;
  case val_undef_false :
  case val_undef_true :
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
void sat_solver_add_binary_clause(sat_solver_t *solver, literal_t l0, literal_t l1) {
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
void sat_solver_add_ternary_clause(sat_solver_t *solver, literal_t l0, literal_t l1, literal_t l2) {
  literal_t lit[3];

  lit[0] = l0;
  lit[1] = l1;
  lit[2] = l2;
  add_clause_core(solver, 3, lit);
}


/*
 * Add a clause of n literals
 */
void sat_solver_add_clause(sat_solver_t *solver, uint32_t n, literal_t *lit) {
  if (n > 2) {
    add_clause_core(solver, n, lit);
  } else if (n == 2) {
    sat_solver_add_binary_clause(solver, lit[0], lit[1]);
  } else if (n == 1) {
    sat_solver_add_unit_clause(solver, lit[0]);
  } else {
    sat_solver_add_empty_clause(solver);
  }
}



/*
 * More careful version: simplify a clause and add it to solver.
 * No effect if sol is already unsat.
 */
void sat_solver_simplify_and_add_clause(sat_solver_t *solver, uint32_t n, literal_t *lit) {
  uint32_t i, j;
  literal_t l, l_aux;

  if (solver->status == status_unsat) return;

  if (n == 0) {
    sat_solver_add_empty_clause(solver);
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
    switch (lit_val(solver, l)) {
    case val_false:
      break;
    case val_undef_false :
    case val_undef_true :
      lit[j] = l;
      j++;
      break;
    default: // true literal, so the clause is true
      return;
    }
  }
  n = j; // new clause size

  sat_solver_add_clause(solver, n, lit);
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
static void increase_clause_activity(sat_solver_t *solver, clause_t *cl) {
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

  // statistics
#if INSTRUMENT_CLAUSES
  learned_clause_created(solver, cl);
#endif

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
 * Sort the learned clauses: use stable sort to give preference to new
 * clauses in case of ties.
 */
static void sort_learned_clauses(sat_solver_t *solver) {
  clause_t **v;

  v = solver->learned_clauses;
  apply_sorter(&solver->sorter,  (void **) v, get_cv_size(v));
}



/*
 * Auxiliary function: follow clause list
 * Remove all clauses marked for deletion
 */
static void cleanup_watch_list(link_t *list) {
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
static bool clause_is_locked(sat_solver_t *solver, clause_t *cl) {
  literal_t l0, l1;

  l0 = get_first_watch(cl);
  l1 = get_second_watch(cl);

  return (lit_is_assigned(solver, l0) &&
          solver->antecedent[var_of(l0)] == mk_clause0_antecedent(cl))
    || (lit_is_assigned(solver, l1) &&
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
#if INSTRUMENT_CLAUSES
      learned_clause_deletion(solver, v[i]);
#endif
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
  float act_threshold;

  assert(get_cv_size(solver->learned_clauses) > 0);

  sort_learned_clauses(solver);

  v = solver->learned_clauses;
  n = get_cv_size(v);


  /*
   * Prepare for deletion: the first half of v contains the low score
   * clauses.
   */
  for (i=0; i<n/2; i++) {
    if (! clause_is_locked(solver, v[i])) {
      mark_for_deletion(v[i]);
    }
  }

  // Delete more
  act_threshold = solver->cla_inc/n;
  for (i = n/2; i<n; i++) {
    if (get_activity(v[i]) <= act_threshold && ! clause_is_locked(solver, v[i])) {
      mark_for_deletion(v[i]);
    }
  }

  delete_learned_clauses(solver);
  solver->stats.reduce_calls ++;
}




/********************************************
 *  SIMPLIFICATION OF THE CLAUSE DATABASE   *
 *******************************************/

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
    switch (lit_val(solver, l)) {
    case val_undef_false:
    case val_undef_true:
      cl->cl[j] = l;
      j ++;
      break;

    case val_true:
      mark_for_deletion(cl);
      return;

    case val_false:
      break;
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
    if (lit_is_unassigned(solver, l)) { //keep l
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
        if (lit_is_unassigned(solver, l1)) {
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
 * Literal corresponding to the assignment or preferred polarity of x
 * - if value[pos_lit(x)] = val_undef_true  --> pos_lit(x)
 * - if value[pos_lit(x)] = val_undef_false --> neg_lit(x)
 */
static inline literal_t preferred_literal(sat_solver_t *solver, bvar_t x) {
  literal_t l;

  l = pos_lit(x);
  return l | (~solver->value[l] & 1);
}


/*
 * Assign x to its preferred value then push the corresponding literal
 * on the propagation stack
 * - x must be unassigned
 */
static void decide_variable(sat_solver_t *solver, bvar_t x) {
  uint32_t d;
  literal_t l;

  assert(var_is_unassigned(solver, x));

  // Increase decision level
  d = solver->decision_level + 1;
  solver->decision_level = d;
  if (solver->stack.nlevels <= d) {
    increase_stack_levels(&solver->stack);
  }
  solver->stack.level_index[d] = solver->stack.top;

  solver->antecedent[x] = mk_literal_antecedent(null_literal);
  solver->level[x] = d;

  l = preferred_literal(solver, x);
  assert(l == pos_lit(x) || l == neg_lit(x));
  solver->value[l] = val_true;
  solver->value[not(l)] = val_false;

  push_literal(&solver->stack, l);

#if TRACE
  printf("---> Decision: literal %d, decision level = %u\n", l, solver->decision_level);
#endif
}



/*
 * Assign literal l to true and attach antecedent a.
 */
static void implied_literal(sat_solver_t *solver, literal_t l, antecedent_t a) {
  bvar_t v;

  assert(lit_is_unassigned(solver, l));

#if TRACE
  printf("---> Implied literal %d, decision level = %u\n", l, solver->decision_level);
#endif

  solver->stats.propagations ++;

  push_literal(&solver->stack, l);

  solver->value[l] = val_true;
  solver->value[not(l)] = val_false;

  v = var_of(not(l));
  solver->antecedent[v] = a;
  solver->level[v] = solver->decision_level;
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
static void record_binary_conflict(sat_solver_t *solver, literal_t l0, literal_t l1) {
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
static void record_clause_conflict(sat_solver_t *solver, clause_t *cl) {
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

  assert(v != NULL && val == sol->value);
  assert(sol->bin[l0] == v && lit_val(sol, l0) == val_false);

  for (;;) {
    // Search for non-true literals in v
    // This terminates since val[end_marker] = VAL_UNDEF
    do {
      l1 = *v ++;
      //      v1 = lit_val(sol, l1);
      v1 = val[l1];
    } while (v1 == val_true);

    if (l1 < 0) break; // end_marker

    if (is_unassigned_val(v1)) {
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
static int propagation_via_watched_list(sat_solver_t *sol, uint8_t *val, link_t *list) {
  bval_t v1;
  clause_t *cl;
  link_t link;
  uint32_t k, i;
  literal_t l1, l, *b;

  assert(val == sol->value);

  link = *list;
  while (link != NULL_LINK) {
    i = idx_of(link);
    cl = clause_of(link);
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
        if (is_unassigned_val(v1)) {
          // l1 is implied
          implied_literal(sol, l1, mk_clause_antecedent(cl, i^1));

#if INSTRUMENT_CLAUSES
	  if (l == end_learned) {
	    learned_clause_prop(sol, cl);
	  }
#endif

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
  literal_t *queue;
  literal_t l, *bin;
  uint32_t i;
  int32_t code;

  queue = sol->stack.lit;

  for (i = sol->stack.prop_ptr; i < sol->stack.top; i++) {
    l = not(queue[i]);
    bin = sol->bin[l];
    if (bin != NULL) {
      code = propagation_via_bin_vector(sol, sol->value, l, bin);
      if (code != no_conflict) {
	return code;
      }
    }

    code = propagation_via_watched_list(sol, sol->value, sol->watch + l);
    if (code != no_conflict) {
      return code;
    }
  }

  sol->stack.prop_ptr = i;

  return no_conflict;
}


/*
 * After propagation at level 0, mark all the implied literals
 */
static void mark_level0_literals(sat_solver_t *solver) {
  uint32_t i, n;
  bvar_t v;

  assert(solver->decision_level == 0);

  n = solver->stack.top;
  for (i=0; i<n; i++) {
    v = var_of(solver->stack.lit[i]);
    set_bit(solver->mark, v);
  }
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
 * - sol->buffer contains the learned clause, with implied literal in sol->buffer.data[0]
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
static uint32_t signature(sat_solver_t *sol, literal_t *b, uint32_t n) {
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
 * - sol->buffer[0] is the implied literal
 */
static void simplify_learned_clause(sat_solver_t *sol) {
  uint32_t hash;
  literal_t *b;
  literal_t l;
  uint32_t i, j, n;


  b = sol->buffer.data;
  n = sol->buffer.size;
  hash = signature(sol, b+1, n-1); // skip b[0]. It cannot be subsumed.

  assert(sol->buffer2.size == 0);

  // remove the subsumed literals
  j = 1;
  for (i=1; i<n; i++) {
    l = b[i];
    if (subsumed(sol, l, hash)) {
      // Hack: move l to buffer2 to clear its mark later
      ivector_push(&sol->buffer2, l);
    } else {
      // keep l in buffer
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

#if DEBUG
#endif

/*
 * Set mark for literal l
 */
static inline void set_var_mark(sat_solver_t *sol, bvar_t x) {
  set_bit(sol->mark, x);
}


/*
 * Process literal l during conflict resolution:
 * - if l is already marked, do nothing
 * - otherwise: mark it + if l has level < conflict level
 *   add l at the end of buffer
 * - return 1 if l is to be resolved (l was not marked and has level == conflict level)
 * - return 0 otherwise
 */
static uint32_t process_literal(sat_solver_t *sol, literal_t l, uint32_t conflict_level) {
  bvar_t x;

  x = var_of(l);
  if (is_var_unmarked(sol, x)) {
    set_var_mark(sol, x);
    increase_var_activity(&sol->heap, x);
    if (sol->level[x] == conflict_level) {
      return 1;
    }
    ivector_push(&sol->buffer, l);
  }
  return 0;
}

/*
 * Search for first UIP and build the learned clause
 * sol = solver state
 *   sol->cl stores a conflict clause (i.e., an array of literals
 *   terminated by -1 with all literals in sol->cl false).
 * result:
 * - the learned clause is stored in sol->buffer as an array of literals
 * - sol->buffer.data[0] is the implied literal
 */
#define process_literal_macro(l)              \
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
    unresolved += process_literal(sol, l, conflict_level);
    c ++;
    l = *c;
  }

  /*
   * If the conflict is a learned clause, increase its activity
   */
  if (l == end_learned) {
    increase_clause_activity(sol, sol->false_clause);
#if INSTRUMENT_CLAUSES
    learned_clause_reso(sol, sol->false_clause);
#endif
  }

  /*
   * Scan the assignment stack from top to bottom and process the
   * antecedent of all marked literals.
   */
  stack = sol->stack.lit;
  j = sol->stack.top;
  for (;;) {
    j --;
    b = stack[j];
    assert(sol->level[var_of(b)] == conflict_level);
    if (is_lit_marked(sol, b)) {
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
          unresolved += process_literal(sol, l, conflict_level);
          // rest of the clause
          c += 2;
          l = *c;
          while (l >= 0) {
	    unresolved += process_literal(sol, l, conflict_level);
            c ++;
            l = *c;
          }
          if (l == end_learned) {
            increase_clause_activity(sol, cl);
#if INSTRUMENT_CLAUSES
	    learned_clause_reso(sol, cl);
#endif
          }
          break;

        case literal_tag:
          l = literal_antecedent(a);
          unresolved += process_literal(sol, l, conflict_level);
          break;

        case generic_tag:
          assert(false);
	  break;
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
 * Select an unassigned literal variable x
 * - returns null_bvar (i.e., -1) if all variables are assigned.
 */
static bvar_t select_variable(sat_solver_t *solver) {
  //  uint32_t rnd;
  bvar_t x;

#if 0
  /*
   * Try a random variable
   */
  rnd = random_uint32() & 0xFFFFFF;
  if (rnd <= (uint32_t) (0x1000000 * VAR_RANDOM_FACTOR)) {
    x = random_uint(solver->nb_vars);
    if (var_is_unassigned(solver, x)) {
#if TRACE
      printf("---> Random selection: literal %d\n", l);
#endif
      solver->stats.decisions ++;
      solver->stats.random_decisions ++;
      return x;
    }
  }
#endif

  /*
   * Select unassigned variable x with highest activity
   */
  while (! heap_is_empty(&solver->heap)) {
    x = heap_get_top(&solver->heap);
    if (var_is_unassigned(solver, x)) {
#if DEBUG
      check_top_var(solver, x);
#endif
      solver->stats.decisions ++;
      return x;
    }
  }

  /*
   * Check the variables in [heap->vmax ... heap->size - 1]
   */
  x = solver->heap.vmax;
  while (x < solver->heap.size) {
    if (var_is_unassigned(solver, x)) {
      solver->stats.decisions ++;
      solver->heap.vmax = x+1;
      return x;
    }
    x ++;
  }

  assert(x == solver->heap.size);
  solver->heap.vmax = x;

  /*
   * All variables are assigned
   */
  return null_bvar;
}


/*
 * Backtrack to the given level
 * - undo all assignments done at levels >= back_level + 1
 * - requires sol->decision_level > back_level, otherwise
 *   level_index[back_level+1] may not be set properly
 */
static void backtrack(sat_solver_t *sol, uint32_t back_level) {
  uint16_t *val;
  uint32_t i;
  uint32_t d;
  literal_t l;
  bvar_t x;

#if TRACE
  printf("---> Backtracking to level %u\n", back_level);
#endif

  assert(back_level < sol->decision_level);

  val = (uint16_t *) sol->value;
  d = sol->stack.level_index[back_level + 1];
  i = sol->stack.top;
  while (i > d) {
    i --;
    l = sol->stack.lit[i];

    assert(lit_val(sol, l) == val_true);
    assert(sol->level[var_of(l)] > back_level);

    // clear assignment (i.e. bit 1) but keep current polarity (i.e. bit 0)
    x = var_of(l);
    val[x] ^= (uint16_t) (0x0202); // flip assign bits of val[l] and val[not(l)]

    assert(lit_val(sol, l) == val_undef_true && lit_val(sol, not(l)) == val_undef_false);

    heap_insert(&sol->heap, x);
  }

  sol->stack.top = i;
  sol->stack.prop_ptr = i;
  sol->decision_level = back_level;

}


/*
 * Check whether all variables assigned at level k have
 * activity less than ax
 */
static bool level_has_lower_activity(sat_solver_t *sol, double ax, uint32_t k) {
  sol_stack_t *stack;
  uint32_t i, n;
  bvar_t x;

  assert(k <= sol->decision_level);
  stack = &sol->stack;

  // i := start of level k
  // n := end of level k
  i = stack->level_index[k];
  n = stack->top;
  if (k < sol->decision_level) {
    n = stack->level_index[k+1];
  }

  while (i < n) {
    x = var_of(stack->lit[i]);
    assert(var_is_assigned(sol, x) && sol->level[x] == k);
    if (sol->heap.activity[x] >= ax) {
      return false;
    }
    i ++;
  }

  return true;
}


/*
 * RESTARTS: THREE VARIANTS
 * - full restart: backtrack(sol, 0)
 * - partial restart: lazier version: backtrack(sol, k) for some
 *   level k >= 0 determined by variable activities:
 * - partial_restart_var: even lazier version: if partial restart
 *   would backtrack to level k then partial_restart_var backtracks
 *   to k' >= k.
 * - benchmarking shows that partial_restart_var seems to work best.
 */

#if 0
/*
 * Partial restart:
 * - find the unassigned variable of highest activity
 * - keep all current decisions that have an activity higher than that
 */
static void partial_restart(sat_solver_t *sol) {
  double ax;
  bvar_t x;
  uint32_t i, k, n;

  assert(sol->decision_level > 0);

  cleanup_heap(sol);
  if (heap_is_empty(&sol->heap)) {
    backtrack(sol, 0); // full restart
  } else {
    x = sol->heap.heap[1]; // top variable
    assert(x >= 0 && var_is_unassigned(sol, x));
    ax = sol->heap.activity[x];

    n = sol->decision_level;
    for (i=1; i<=n; i++) {
      k = sol->stack.level_index[i];
      x = var_of(sol->stack.lit[k]);  // decision variable for level i
      assert(var_is_assigned(sol, x) &&
	     sol->level[x] == i &&
	     sol->antecedent[x] == mk_literal_antecedent(null_literal));
      if (sol->heap.activity[x] < ax) {
	backtrack(sol, i - 1);
	break;
      }
    }
  }
}
#endif

/*
 * Variant:
 * - find the unassigned variable of highest activity
 * - keep all current decision levels that have at least one variable
 *   with highest activity than that
 */
static void partial_restart_var(sat_solver_t *sol) {
  double ax;
  bvar_t x;
  uint32_t i, n;

  assert(sol->decision_level > 0);
  cleanup_heap(sol);
  if (heap_is_empty(&sol->heap)) {
    backtrack(sol, 0); // full restart
  } else {
    x = sol->heap.heap[1];
    assert(x >= 0 && var_is_unassigned(sol, x));
    ax = sol->heap.activity[x];

    n = sol->decision_level;
    for (i=1; i<=n; i++) {
      if (level_has_lower_activity(sol, ax, i)) {
	backtrack(sol, i-1);
	break;
      }
    }
  }
}


/*
 * TEMPORARY
 */
#if INSTRUMENT_CLAUSES
static uint32_t next_snapshot;
#endif


/*
 * Search until the given number of conflict is reached.
 * - sol: solver
 * - conflict_bound: number of conflict
 * output: status_sat, status_unsolved, or status_unsat
 */
solver_status_t sat_search(sat_solver_t *sol, uint32_t conflict_bound) {
  int32_t code;
  literal_t l, *b;
  bvar_t x;
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
	  // restart
	  partial_restart_var(sol);
        }
        return status_unsolved;
      }

      // At level 0: mark literals + simplify
      if (sol->decision_level == 0) {
	mark_level0_literals(sol);

	if (sol->stack.top > sol->simplify_bottom &&
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
      }

#if INSTRUMENT_CLAUSES
      if (sol->stats.conflicts >= next_snapshot) {
	snapshot(sol);
	do {
	  next_snapshot += 10000;
	} while (next_snapshot < sol->stats.conflicts);
      }
#endif

      // Delete half the learned clauses if the threshold is reached
      // then increase the threshold
      if (get_cv_size(sol->learned_clauses) >= sol->reduce_threshold + sol->stack.top) {
        reduce_learned_clause_set(sol);
	sol->reduce_threshold = (uint32_t) (sol->reduce_threshold * REDUCE_FACTOR);
	//	sol->reduce_threshold += INCR_REDUCE_THRESHOLD;
      }

      x = select_variable(sol);
      if (x < 0) {
        sol->status = status_sat;
        return status_sat;
      }

      // assign x to its preferred polarity
      // then push the corresponding literal in the queue
      decide_variable(sol, x);

    } else {
      sol->stats.conflicts ++;
      nb_conflicts ++;

      // Check if UNSAT
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
#if INSTRUMENT_CLAUSES
	// EXPERIMENTAL
	learned_clause_prop(sol, cl);
#endif

      } else if (n == 2) {
        sat_solver_add_binary_clause(sol, l, b[1]);
        implied_literal(sol, l, mk_literal_antecedent(b[1]));

      } else {
        assert(n > 0);

        sat_solver_add_unit_clause(sol, l);
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
solver_status_t solve(sat_solver_t *sol, bool verbose) {
  int32_t code;
  //  uint32_t c_threshold, d_threshold;
  uint32_t u, v, threshold;

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

  /*
   * restart strategy based on picosat
   */
  // c_threshold = number of conflicts in each iteration
  // increased by RETART_FACTOR after each iteration
#if 0
  c_threshold = INITIAL_RESTART_THRESHOLD;
  d_threshold = INITIAL_RESTART_THRESHOLD;
#endif

  /*
   * Restart strategy: Luby sequence
   */
#if 1
  u = 1;
  v = 1;
  threshold = LUBY_INTERVAL;
#endif

  /*
   * Reduce strategy: like minisat
   */
  //  sol->reduce_threshold = UINT32_MAX;
  sol->reduce_threshold = sol->nb_clauses/4;
  if (sol->reduce_threshold < MIN_REDUCE_THRESHOLD) {
    sol->reduce_threshold = MIN_REDUCE_THRESHOLD;
  }

#if INSTRUMENT_CLAUSES
  next_snapshot = 10000;
#endif

  if (verbose) {
    fprintf(stderr, "---------------------------------------------------------------------------------\n");
    fprintf(stderr, "|     Thresholds    |  Binary   |      Original     |          Learned          |\n");
    fprintf(stderr, "|   Conf.      Del. |  Clauses  |   Clauses   Lits. |   Clauses  Lits. Lits/Cl. |\n");
    fprintf(stderr, "---------------------------------------------------------------------------------\n");

    fprintf(stderr, "| %7"PRIu32"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu64" | %8"PRIu32" %8"PRIu64" %7.1f |\n",
	    //	    d_threshold, sol->reduce_threshold, sol->nb_bin_clauses,              // PICO
	    threshold, sol->reduce_threshold, sol->nb_bin_clauses,  // LUBY
            get_cv_size(sol->problem_clauses), sol->stats.prob_literals,
            get_cv_size(sol->learned_clauses), sol->stats.learned_literals,
            ((double) sol->stats.learned_literals)/get_cv_size(sol->learned_clauses));
    fflush(stderr);
  }

  do {
#if DEBUG
    check_marks(sol);
#endif
    //    code = sat_search(sol, c_threshold);  // PICO
    code = sat_search(sol, threshold);     // LUBY

#if DEBUG
    check_marks(sol);
#endif

#if 1
    // Luby sequence
    if ((u & -u) == v) {
      u ++;
      v = 1;
    } else {
      v <<= 1;
    }
    threshold = v * LUBY_INTERVAL;
    if (verbose) {
      fprintf(stderr, "| %7"PRIu32"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu64" | %8"PRIu32" %8"PRIu64" %7.1f |\n",
	      threshold, sol->reduce_threshold, sol->nb_bin_clauses,
	      get_cv_size(sol->problem_clauses), sol->stats.prob_literals,
	      get_cv_size(sol->learned_clauses), sol->stats.learned_literals,
	      ((double) sol->stats.learned_literals)/get_cv_size(sol->learned_clauses));
      fflush(stderr);
    }
#endif

#if 0
    // picosat-style sequence
    c_threshold = (uint32_t)(c_threshold * RESTART_FACTOR);  // multiply by 1.1
    if (c_threshold >= d_threshold) {
      c_threshold = INITIAL_RESTART_THRESHOLD;
      d_threshold = (uint32_t)(d_threshold * RESTART_FACTOR);
      if (verbose) {
        fprintf(stderr, "| %7"PRIu32"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu64" | %8"PRIu32" %8"PRIu64" %7.1f |\n",
                d_threshold, sol->reduce_threshold, sol->nb_bin_clauses,
                get_cv_size(sol->problem_clauses), sol->stats.prob_literals,
                get_cv_size(sol->learned_clauses), sol->stats.learned_literals,
                ((double) sol->stats.learned_literals)/get_cv_size(sol->learned_clauses));
        fflush(stderr);
      }
      if (d_threshold > MAX_DTHRESHOLD) {
        d_threshold = MAX_DTHRESHOLD;
      }
    }
#endif


  } while (code == status_unsolved);

  if (verbose) {
    fprintf(stderr, "---------------------------------------------------------------------------------\n");
    fflush(stderr);
  }

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
    if (lit_val(solver, l) == val_true) {
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
 * Inline functions used only here: they can cause compilation warning
 * (clang is getting picky)
 */
static inline uint32_t get_lv_capacity(literal_t *v) {
  return lv_header(v)->capacity;
}

static inline bool is_var_marked(sat_solver_t *sol, bvar_t x) {
  return tst_bit(sol->mark, x) != 0;
}


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
    if (var_is_unassigned(solver,y) && heap->activity[y] > heap->activity[x]) {
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

  v = sol->bin[l0];

  if (v == NULL || lit_val(sol,l0) != val_false) return;

  l1 = *v ++;
  while (l1 >= 0) {
    if (lit_is_unassigned(sol,l1)) {
      printf("ERROR: missed propagation. Binary clause {%d, %d}\n", l0, l1);
    } else if (lit_val(sol,l1) == val_false) {
      printf("ERROR: missed conflict. Binary clause {%d, %d}\n", l0, l1);
    }
    l1 = *v ++;
  }
}

static int32_t indicator(bval_t v, bval_t c) {
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
  nf += indicator(lit_val(sol, l0), val_false);
  nt += indicator(lit_val(sol, l0), val_true);
  nu += indicator(lit_val(sol, l0), val_undef_false);
  nu += indicator(lit_val(sol, l0), val_undef_true);

  l1 = get_second_watch(cl);
  nf += indicator(lit_val(sol, l1), val_false);
  nt += indicator(lit_val(sol, l1), val_true);
  nu += indicator(lit_val(sol, l1), val_undef_false);
  nu += indicator(lit_val(sol, l1), val_undef_true);

  d = cl->cl;
  i = 2;
  l = d[i];
  while (l >= 0) {
    nf += indicator(lit_val(sol, l), val_false);
    nt += indicator(lit_val(sol, l), val_true);
    nu += indicator(lit_val(sol, l), val_undef_false);
    nu += indicator(lit_val(sol, l), val_undef_true);

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
