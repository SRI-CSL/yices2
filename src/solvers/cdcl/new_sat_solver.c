/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STAND-ALONE SAT SOLVER
 */

#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include <float.h>

#include "solvers/cdcl/new_sat_solver.h"
#include "solvers/cdcl/sat_parameters.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"



/*
 * Set these flags to 1 for debugging and trace
 */
#define DEBUG 0
#define TRACE 0


/*
 * DEBUG
 */
#if DEBUG
/*
 * The following functions checks internal consistency. They are defined 
 * at the end of this file. They print an error on stderr if the checks fail.
 */
static void clause_pool_check_counters(const clause_pool_t *pool);
static void check_heap(const var_heap_t *heap);

#else
/*
 * Place holders: do nothing
 */
static inline void clause_pool_check_counters(const clause_pool_t *pool) { }
static inline void check_heap(const var_heap_t *heap) { }
#endif



/**********
 *  PRNG  *
 *********/

/*
 * PARAMETERS FOR THE PSEUDO RANDOM NUMBER GENERATOR
 *
 * We  use the same linear congruence as in prng.h,
 * but we use a local implementation so that different
 * solvers can use different seeds.
 */

#define PRNG_MULTIPLIER 1664525
#define PRNG_CONSTANT   1013904223
#define PRNG_SEED       0xabcdef98


/*
 * Return a 32bit unsigned int
 */
static inline uint32_t random_uint32(sat_solver_t *s) {
  uint32_t x;

  x = s->prng;
  s->prng = x * ((uint32_t) PRNG_MULTIPLIER) + ((uint32_t) PRNG_CONSTANT);
  return x;
}


/*
 * Return a 32bit integer between 0 and n-1
 */
static inline uint32_t random_uint(sat_solver_t *s, uint32_t n) {
  return (random_uint32(s) >> 8) % n;
}



/******************
 *  CLAUSE POOL   *
 *****************/

/*
 * Capacity increase:
 * cap += ((cap >> 1) + (cap >> 6) + (cap >> 7) + 2048) & ~3
 *
 * Since the intiail capacity is 262144, we get an increasing
 * sequence: 262144, 401408, 613568,  ..., 4265187980,
 * which gets us close to 2^32.  The next increase after that
 * causes an arithmetic overflow.
 */
static inline uint32_t pool_cap_increase(uint32_t cap) {
  return ((cap >> 1) + (cap >> 6) + (cap >> 7) + 2048) & ~3;
}

/*
 * Maximal capacity after reset.
 * On a call to reset, we try to save memory by reducing
 * the pool capacity to this. This size is what we'd get
 * after 14 rounds on pool_cal_increase (about 126 MB).
 */
#define RESET_CLAUSE_POOL_CAPACITY 33155608

/*
 * Some consistency checks
 */
#ifndef NDEBUG
static bool is_multiple_of_four(uint32_t x) {
  return (x & 3) == 0;
}

static bool clause_pool_invariant(clause_pool_t *pool) {
  return 
    pool->learned <= pool->size &&
    pool->size <= pool->capacity &&
    pool->available == pool->capacity - pool->size &&
    is_multiple_of_four(pool->learned) &&
    is_multiple_of_four(pool->size) &&
    is_multiple_of_four(pool->capacity);
}
#endif

/*
 * Global operations
 */
static void init_clause_pool(clause_pool_t *pool) {
  uint32_t *tmp;

  tmp = (uint32_t *) malloc(DEF_CLAUSE_POOL_CAPACITY * sizeof(uint32_t));
  if (tmp == NULL) {
    out_of_memory();
  }

  pool->data = tmp;
  pool->learned = 0;
  pool->size = 0;
  pool->capacity = DEF_CLAUSE_POOL_CAPACITY;
  pool->available = DEF_CLAUSE_POOL_CAPACITY;

  pool->num_prob_clauses = 0;
  pool->num_prob_literals = 0;
  pool->num_learned_clauses = 0;
  pool->num_learned_literals = 0;

  assert(clause_pool_invariant(pool));
}

static void delete_clause_pool(clause_pool_t *pool) {
  assert(clause_pool_invariant(pool));
  free(pool->data);
  pool->data = NULL;
}

static void reset_clause_pool(clause_pool_t *pool) {
  uint32_t *tmp;

  assert(clause_pool_invariant(pool));

  if (pool->capacity > RESET_CLAUSE_POOL_CAPACITY) {
    free(pool->data);
    tmp = (uint32_t *) malloc(RESET_CLAUSE_POOL_CAPACITY * sizeof(uint32_t));
    if (tmp == NULL) {
      out_of_memory();
    }
    pool->data = tmp;
    pool->capacity = RESET_CLAUSE_POOL_CAPACITY;
  }

  pool->learned = 0;
  pool->size = 0;
  pool->available = pool->capacity;


  pool->num_prob_clauses = 0;
  pool->num_prob_literals = 0;
  pool->num_learned_clauses = 0;
  pool->num_learned_literals = 0;

  assert(clause_pool_invariant(pool));
}


/*
 * Make sure there's enough room for allocating n elements
 * - this should be called only when resize is required
 */
static void resize_clause_pool(clause_pool_t *pool, uint32_t n) {
  uint32_t min_cap, cap, increase;
  uint32_t *tmp;

  assert(clause_pool_invariant(pool));

  min_cap = pool->size + n;
  if (min_cap < n || min_cap > MAX_CLAUSE_POOL_CAPACITY) {
    // can't make the pool large enough
    out_of_memory();
  }

  cap = pool->capacity;
  do {
    increase = pool_cap_increase(cap);
    cap += increase;
    if (cap < increase) { // arithmetic overfow
      cap = MAX_CLAUSE_POOL_CAPACITY;
    }
  } while (cap < min_cap);

  tmp = (uint32_t *) realloc(pool->data, cap * sizeof(uint32_t));
  if (tmp == NULL) {
    out_of_memory();
  }

  pool->data = tmp;
  pool->capacity = cap;
  pool->available = cap - pool->size;

  assert(clause_pool_invariant(pool));
}


/*
 * Allocate an array of n integers in the pool and return its idx
 */
static cidx_t clause_pool_alloc_array(clause_pool_t *pool, uint32_t n) {
  cidx_t i;

  assert(clause_pool_invariant(pool));

  n = (n + 3) & ~3; // round up to the next multiple of 4
  if (n > pool->available) {
    resize_clause_pool(pool, n);
  }
  assert(n <= pool->available);

  i = pool->size;
  pool->size += n;
  pool->available -= n;

  assert(clause_pool_invariant(pool));

  return i;
}


/*
 * Initialize the clause that start at index cidx:
 * - set the header: length = n, aux = 0
 * - copy the literals 
 */
static void clause_pool_init_clause(clause_pool_t *pool, cidx_t cidx, uint32_t n, const literal_t *a) {
  uint32_t i;
  uint32_t *p;

  pool->data[cidx] = n;
  pool->data[cidx + 1] = 0;
  p = pool->data + cidx + 2;
  for (i=0; i<n; i++) {
    p[i] = a[i];
  }
}

/*
 * Add a problem clause
 */
static cidx_t clause_pool_add_problem_clause(clause_pool_t *pool, uint32_t n, const literal_t *a) {
  uint32_t cidx;

  assert(pool->learned == pool->size);

  cidx = clause_pool_alloc_array(pool, n+2);
  clause_pool_init_clause(pool, cidx, n, a);

  pool->num_prob_clauses ++;
  pool->num_prob_literals += n;
  pool->learned = pool->size;

  clause_pool_check_counters(pool);

  return cidx;
}

/*
 * Add a learned clause
 */
static cidx_t clause_pool_add_learned_clause(clause_pool_t *pool, uint32_t n, const literal_t *a) {
  uint32_t cidx;

  cidx = clause_pool_alloc_array(pool, n+2);
  clause_pool_init_clause(pool, cidx, n, a);

  pool->num_learned_clauses ++;
  pool->num_learned_literals += n;

  clause_pool_check_counters(pool);

  return cidx;
}


/*
 * Set/read/increase the activity of a learned clause.
 */
static inline void set_learned_clause_activity(clause_pool_t *pool, cidx_t cidx, float act) {
  clause_t *c;
  assert(is_learned_clause_idx(pool, cidx) && sizeof(float) == sizeof(uint32_t));
  c = clause_of_idx(pool, cidx);
  c->aux.f = act;
}

static inline float get_learned_clause_activity(clause_pool_t *pool, cidx_t cidx) {
  clause_t *c;
  assert(is_learned_clause_idx(pool, cidx) && sizeof(float) == sizeof(uint32_t));
  c = clause_of_idx(pool, cidx);
  return c->aux.f;
}

static inline void increase_learned_clause_activity(clause_pool_t *pool, cidx_t cidx, float incr) {
  clause_t *c;
  assert(is_learned_clause_idx(pool, cidx) && sizeof(float) == sizeof(uint32_t));
  c = clause_of_idx(pool, cidx);
  c->aux.f += incr;
}

/*
 * Multiply by scale
 */
static inline void multiply_learned_clause_activity(clause_pool_t *pool, cidx_t cidx, float scale) {
  clause_t *c;
  assert(is_learned_clause_idx(pool, cidx) && sizeof(float) == sizeof(uint32_t));
  c = clause_of_idx(pool, cidx);
  c->aux.f *= scale;
}


/*
 * Full size of a clause with n literals:
 * - 2 + n rounded up to the next multiple of four
 */
static inline uint32_t full_length(uint32_t n) {
  return (n + 5) & ~3;
}


/*
 * Full size of the clause that starts at index i
 */
static inline uint32_t clause_full_length(clause_pool_t *pool, uint32_t i) {
  assert(good_clause_idx(pool, i));
  return full_length(pool->data[i]);
}


/*
 * Check whether i is the start of a padding block
 */
static inline bool is_padding_start(clause_pool_t *pool, uint32_t i) {
  assert(i < pool->size && is_multiple_of_four(i));
  return pool->data[i] == 0;
}

/*
 * Length of the padding block that starts at index i
 */
static inline uint32_t padding_length(clause_pool_t *pool, uint32_t i) {
  assert(is_padding_start(pool, i));
  return pool->data[i+1];
}


/*
 * Store a padding block of size n at index i
 */
static void clause_pool_padding(clause_pool_t *pool, uint32_t i, uint32_t n) {
  uint32_t j;

  assert(i < pool->size && is_multiple_of_four(i) 
	 && is_multiple_of_four(n) && n > 0);

  j = i+n;

  if (j == pool->size) {
    // i is the last block
    pool->size = i;
    if (pool->learned == j) {
      pool->learned = i;
    }
  } else {
    if (is_padding_start(pool, j)) {
      // merge the two padding blocks
      n += padding_length(pool, j);
    }
    pool->data[i] = 0;
    pool->data[i+1] = n;
  }
}


/*
 * Delete the clause that start at index idx
 */
static void clause_pool_delete_clause(clause_pool_t *pool, cidx_t idx) {
  uint32_t n;

  assert(good_clause_idx(pool, idx) && pool->learned > 0);

  n = pool->data[idx]; // clause length
  clause_pool_padding(pool, idx, n);

  // update the statistics
  if (is_problem_clause_idx(pool, idx)) {
    assert(pool->num_prob_clauses > 0);
    assert(pool->num_prob_literals >= n);
    pool->num_prob_clauses --;
    pool->num_prob_literals -= n;
  } else {
    assert(pool->num_learned_clauses > 0);
    assert(pool->num_learned_literals >= n);
    pool->num_learned_clauses --;
    pool->num_learned_literals -= n;
  }

  clause_pool_check_counters(pool);
}


/*
 * Shrink clause idx: n = new size
 */
static void clause_pool_shrink_clause(clause_pool_t *pool, cidx_t idx, uint32_t n) {
  uint32_t old_n, old_len, new_len;

  assert(good_clause_idx(pool, idx) && pool->learned > 0 && 
	 n >= 2 && n <= clause_length(pool, idx));

  old_n = clause_length(pool, idx);
  old_len = full_length(old_n);
  new_len = full_length(n);

  assert(new_len <= old_len);
  if (new_len < old_len) {
    clause_pool_padding(pool, idx + new_len, old_len - new_len);
  }

  pool->data[idx] = n;

  if (is_problem_clause_idx(pool, idx)) {
    assert(pool->num_prob_clauses > 0);
    assert(pool->num_prob_literals >= old_n);
    pool->num_prob_literals -= (old_n - n);
  } else {
    assert(pool->num_learned_clauses > 0);
    assert(pool->num_learned_literals >= old_n);
    pool->num_learned_literals -= (old_n - n);
  }

  clause_pool_check_counters(pool);
}


/*
 * Find the next clause, scanning from index i
 * - i may be the start of a clause or of a padding block
 */
static cidx_t next_clause_index(clause_pool_t *pool, cidx_t i) {
  while (i < pool->size && is_padding_start(pool, i)) {
    i += padding_length(pool, i);
  }
  return i;
}


/*
 * First clause
 */
static inline cidx_t clause_pool_first_clause(clause_pool_t *pool) {
  return next_clause_index(pool, 0);
}

/*
 * First learned clause
 */
static inline cidx_t clause_pool_first_learned_clause(clause_pool_t *pool) {
  return next_clause_index(pool, pool->learned);
}

/*
 * Clause that follows idx
 */
static inline cidx_t clause_pool_next_clause(clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return next_clause_index(pool, idx + clause_full_length(pool, idx));
}


/*****************
 *  WATCH LISTS  *
 ****************/

/*
 * Capacity increase for watch vectors:
 * - about 50% increase, rounded up to force the increment to be a multiple of four
 */
static inline uint32_t watch_cap_increase(uint32_t cap) {
  return ((cap >> 1) + 8) & ~3;
}

/*
 * Add k at the end of vector *w.
 * - if *w is NULL, allocate a vector of default size
 * - if *w if full, make it 50% larger.
 */
static void add_watch(watch_t **w, uint32_t k) {
  watch_t *v;
  uint32_t i, n;

  v = *w;
  if (v == NULL) {
    i = 0;
    n = DEF_WATCH_CAPACITY;
    v = (watch_t *) safe_malloc(sizeof(watch_t) + n * sizeof(uint32_t));
    v->capacity = n;
    *w = v;
  } else {
    i = v->size;
    n = v->capacity;
    if (i == n) {
      n += watch_cap_increase(n);
      if (n > MAX_WATCH_CAPACITY) {
	out_of_memory();
      }
      v = (watch_t *) safe_realloc(v, sizeof(watch_t) + n * sizeof(uint32_t));
      v->capacity = n;
      *w = v;
    }
  }
  assert(i < v->capacity);
  v->data[i] = k;
  v->size = i+1;
}



/*
 * Delete all watch vectors in w[0 ... n-1]
 */
static void delete_watch_vectors(watch_t **w, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    safe_free(w[i]);
    w[i] = NULL;
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
  s->lit = NULL;
  s->level_index = NULL;
}


/*
 * Empty the stack
 */
static void reset_stack(sol_stack_t *s) {
  s->top = 0;
  s->prop_ptr = 0;
  assert(s->level_index[0] == 0);
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
 * - heap[0] = 0 is a marker, with activity[0] higher
 *   than any variable activity.
 * - activity increment and threshold are set to their
 *   default initial value.
 */
static void init_heap(var_heap_t *heap, uint32_t n) {
  uint32_t i;
  double *tmp;

  tmp = (double *) safe_malloc((n + 1) * sizeof(double));
  heap->activity = tmp + 1;
  heap->heap_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  heap->heap = (bvar_t *) safe_malloc(n * sizeof(bvar_t));

  // markers
  heap->activity[-1] = -1.0;
  heap->activity[0] = DBL_MAX;  
  heap->heap_index[0] = 0;
  heap->heap[0] = 0;

  for (i=1; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }

  heap->heap_last = 0;
  heap->size = n;
  heap->vmax = 1;

  heap->act_increment = INIT_VAR_ACTIVITY_INCREMENT;
  heap->inv_act_decay = 1/VAR_DECAY_FACTOR;

  check_heap(heap);
}


/*
 * Extend the heap for n variables
 */
static void extend_heap(var_heap_t *heap, uint32_t n) {
  uint32_t old_size, i;
  double *tmp;

  old_size = heap->size;
  assert(old_size < n);
  tmp = heap->activity - 1;
  tmp = (double *) safe_realloc(tmp, (n + 1) * sizeof(double));
  heap->activity = tmp + 1;
  heap->heap_index = (int32_t *) safe_realloc(heap->heap_index, n * sizeof(int32_t));
  heap->heap = (bvar_t *) safe_realloc(heap->heap, n * sizeof(int32_t));
  heap->size = n;

  for (i=old_size; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }

  check_heap(heap);
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
 * Reset: empty the heap
 */
static void reset_heap(var_heap_t *heap) {
  uint32_t i, n;

  heap->heap_last = 0;
  heap->vmax = 1;

  n = heap->size;
  for (i=1; i<n; i++) {
    heap->heap_index[i] = -1;
    heap->activity[i] = 0.0;
  }
  check_heap(heap);
}


/*
 * Move x up in the heap.
 * i = current position of x in the heap (or heap_last if x is being inserted)
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

  check_heap(heap);
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
  if (last <= 1) { // empty heap.
    assert(heap->heap_last == 0);
    return;
  }

  h = heap->heap;
  index = heap->heap_index;
  act = heap->activity;

  z = h[last];   // last element
  h[last] = -1;  // set end marker: act[-1] is negative
  az = act[z];   // activity of the last element

  i = 1;      // root
  j = 2;      // left child of i
  while (j < last) {
    /*
     * find child of i with highest activity.
     * Since h[last] = -1, we don't check j+1 < last
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

  check_heap(heap);
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



/*********************************
 *  SAT SOLVER INIITIALIZATION   *
 ********************************/

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
  stat->prob_clauses_deleted = 0;
  stat->learned_clauses_deleted = 0;
  stat->literals_before_simpl = 0;
  stat->subsumed_literals = 0;
}


/*
 * Initialization:
 * - sz = initial size of the variable-indexed arrays.
 * - if sz is zero, the default size is used.
 * - the solver is initialized with one variable (the reserved variable 0).
 */
void init_nsat_solver(sat_solver_t *solver, uint32_t sz) {
  uint32_t n;

  if (sz > MAX_VARIABLES) {
    out_of_memory();
  }

  n = sz;
  if (sz == 0) {
    n = SAT_SOLVER_DEFAULT_VSIZE;
  }
  assert(n >= 1 && n <= MAX_VARIABLES);

  solver->status = STAT_UNKNOWN;
  solver->decision_level = 0;
  solver->backtrack_level = 0;
  solver->prng = PRNG_SEED;

  solver->nvars = 1;
  solver->nliterals = 2;
  solver->vsize = n;
  solver->lsize = 2 * n;

  solver->value = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  solver->ante_tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  solver->ante_data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  solver->level = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  solver->watch = (watch_t **) safe_malloc(n * 2 * sizeof(watch_t *));

  // variable 0: true
  solver->value[0] = BVAL_TRUE;
  solver->ante_tag[0] = ATAG_UNIT;
  solver->ante_data[0] = 0;
  solver->level[0] = 0;
  solver->watch[0] = NULL;
  solver->watch[1] = NULL;

  init_heap(&solver->heap, n);
  init_stack(&solver->stack, n);

  solver->cla_inc = INIT_CLAUSE_ACTIVITY_INCREMENT;
  solver->inv_cla_decay = ((float) 1)/CLAUSE_DECAY_FACTOR;
  solver->has_empty_clause = false;
  solver->units = 0;
  solver->binaries = 0;
  init_clause_pool(&solver->pool);

  init_stats(&solver->stats);
}


/*
 * Set the prng seed
 */
void nsat_solver_set_seed(sat_solver_t *solver, uint32_t seed) {
  solver->prng = seed;
}


/*
 * Free memory
 */
void delete_nsat_solver(sat_solver_t *solver) {
  safe_free(solver->value);
  safe_free(solver->ante_tag);
  safe_free(solver->ante_data);
  safe_free(solver->level);
  delete_watch_vectors(solver->watch, solver->nliterals);
  safe_free(solver->watch);

  solver->value = NULL;
  solver->ante_tag = NULL;
  solver->ante_data = NULL;
  solver->level = NULL;
  solver->watch = NULL;

  delete_heap(&solver->heap);
  delete_stack(&solver->stack);
  delete_clause_pool(&solver->pool);
}


/*
 * Reset: remove all variables and clauses
 */
void reset_nsat_solver(sat_solver_t *solver) {
  solver->status = STAT_UNKNOWN;
  solver->decision_level = 0;
  solver->backtrack_level = 0;
  solver->nvars = 1;
  solver->nliterals = 2;

  reset_heap(&solver->heap);
  reset_stack(&solver->stack);

  solver->has_empty_clause = false;
  solver->units = 0;
  solver->binaries = 0;
  reset_clause_pool(&solver->pool);

  init_stats(&solver->stats);
}



/********************
 *  ADD VARIABLES   *
 *******************/

/*
 * Extend data structures: new_size = new vsize
 */
static void sat_solver_extend(sat_solver_t *solver, uint32_t new_size) {
  if (new_size > MAX_VARIABLES) {
    out_of_memory();
  }

  solver->vsize = new_size;
  solver->lsize = 2 * new_size;

  solver->value = (uint8_t *) safe_realloc(solver->value, new_size * sizeof(uint8_t));
  solver->ante_tag = (uint8_t *) safe_realloc(solver->ante_tag, new_size * sizeof(uint8_t));
  solver->ante_data = (uint32_t *) safe_realloc(solver->ante_data, new_size * sizeof(uint32_t));
  solver->level = (uint32_t *) safe_realloc(solver->level, new_size * sizeof(uint32_t));
  solver->watch = (watch_t **) safe_realloc(solver->watch, new_size * 2 * sizeof(watch_t *));

  extend_heap(&solver->heap, new_size);
  extend_stack(&solver->stack, new_size);
}


/*
 * Add n variables
 */
void nsat_solver_add_vars(sat_solver_t *solver, uint32_t n) {
  uint32_t i, nv, new_size;

  nv = solver->nvars + n;
  if (nv  < n) {
    // arithmetic overflow: too many variables
    out_of_memory();
  }

  if (nv > solver->vsize) {
    new_size = solver->vsize + 1;
    new_size += new_size >> 1;
    if (new_size < nv) {
      new_size = nv;
    }
    sat_solver_extend(solver, new_size);
    assert(nv <= solver->vsize);
  }

  for (i=solver->nvars; i<n; i++) {
    solver->value[i] = BVAL_UNDEF_FALSE; // default preferrence
    solver->ante_tag[i] = ATAG_NONE;
    solver->ante_data[i] = 0;
    solver->level[i] = UINT32_MAX;
    solver->watch[pos(i)] = NULL;
    solver->watch[neg(i)] = NULL;
  }

  solver->nvars = nv;
  solver->nliterals = 2 * nv;
}


/*
 * Allocate and return a fresh Boolean variable
 */
bvar_t nsat_solver_new_var(sat_solver_t *solver) {
  bvar_t x;

  x = solver->nvars;
  nsat_solver_add_vars(solver, 1);
  assert(solver->nvars == x + 1);
  return x;
}



/*******************
 *  WATCH VECTORS  *
 ******************/

/*
 * Encode l as a watch index
 */
static inline uint32_t lit2idx(literal_t l) {
  return (l << 1) | 1;
}

/*
 * Add clause index in the watch vector for literal l
 */
static inline void add_clause_watch(sat_solver_t *solver, literal_t l, cidx_t cidx) {
  assert(l < solver->nliterals);
  add_watch(solver->watch + l, cidx);
}

/*
 * Add literal l1 in the watch vector for l
 */
static inline void add_literal_watch(sat_solver_t *solver, literal_t l, literal_t l1) {
  assert(l < solver->nliterals);
  add_watch(solver->watch + l, lit2idx(l1));
}



/**********************
 *  CLAUSE ADDITION   *
 *********************/

/*
 * Assign literal l at base level
 */
static void assign_literal(sat_solver_t *solver, literal_t l) {
  bvar_t v;

#if TRACE
  printf("---> Assigning literal %"PRIu32"\n", l);
#endif

  assert(l < solver->nliterals);
  assert(lit_is_unassigned(solver, l));
  assert(solver->decision_level == 0);

  push_literal(&solver->stack, l);

  v = var_of(l);
  // value of v = BVAL_TRUE if l = pos(v) or BVAL_FALSE if l = neg(v)
  solver->value[v] = BVAL_TRUE ^ sign_of(l);
  solver->ante_tag[v] = ATAG_UNIT;
  solver->ante_data[v] = 0;
  solver->level[v] = 0;

  assert(lit_is_true(solver, l));
}


/*
 * Add the empty clause
 */
void nsat_solver_add_empty_clause(sat_solver_t *solver) {
  solver->has_empty_clause = true;
}


/*
 * Add unit clause { l }: push l on the assignment stack
 * or add the empty clause if l is already false
 */
void nsat_solver_add_unit_clause(sat_solver_t *solver, literal_t l) {
#if TRACE
  printf("---> Add unit clause: { %"PRIu32" }\n", l);
#endif

  assert(l < solver->nliterals);

  switch (lit_value(solver, l)) {
  case BVAL_FALSE:
    solver->has_empty_clause = true;
    break;
  case BVAL_UNDEF_FALSE :
  case BVAL_UNDEF_TRUE :
    assign_literal(solver, l);
    solver->units ++;
    break;
  default: // val_true: nothing to do
    break;
  }
}

/*
 * Add an n-literal clause when n >= 2
 */
static void add_clause_core(sat_solver_t *solver, uint32_t n, const literal_t *lit) {
  cidx_t cidx;

  assert(n >= 2);

#ifndef NDEBUG
  // check that all literals are valid
  for (uint32_t i=0; i<n; i++) {
    assert(lit[i] < solver->nliterals);
  }
#endif

  if (n == 2) {
    solver->binaries ++;
    add_literal_watch(solver, lit[0], lit[1]);
    add_literal_watch(solver, lit[1], lit[0]);
  } else {
    cidx = clause_pool_add_problem_clause(&solver->pool, n, lit);
    add_clause_watch(solver, lit[0], cidx);
    add_clause_watch(solver, lit[1], cidx);
  }
}


/*
 * Add clause { l0, l1 }
 */
void nsat_solver_add_binary_clause(sat_solver_t *solver, literal_t l0, literal_t l1) {
  solver->binaries ++;
  add_literal_watch(solver, l0, l1);
  add_literal_watch(solver, l1, l0);  
}


/*
 * Add three-literal clause {l0, l1, l2}
 */
void nsat_solver_add_ternary_clause(sat_solver_t *solver, literal_t l0, literal_t l1, literal_t l2) {
  literal_t lit[3];

  lit[0] = l0;
  lit[1] = l1;
  lit[2] = l2;
  add_clause_core(solver, 3, lit);
}


/*
 * Add a clause of n literals
 */
void nsat_solver_add_clause(sat_solver_t *solver, uint32_t n, const literal_t *lit) {
  if (n > 2) {
    add_clause_core(solver, n, lit);
  } else if (n == 2) {
    nsat_solver_add_binary_clause(solver, lit[0], lit[1]);
  } else if (n == 1) {
    nsat_solver_add_unit_clause(solver, lit[0]);
  } else {
    nsat_solver_add_empty_clause(solver);
  }
}


/*
 * Simplify the clause then add it
 * - n = number of literals
 * - l = array of n literals
 * - the array is modified
 */
void nsat_solver_simplify_and_add_clause(sat_solver_t *solver, uint32_t n, literal_t *lit) {
  uint32_t i, j;
  literal_t l, l_aux;

  if (n == 0) {
    nsat_solver_add_empty_clause(solver);
    return;
  }

  /*
   * Remove duplicates and check for opposite literals l, not(l)
   * (sorting ensure that not(l) is just after l)
   */
  int_array_sort((int32_t *) lit, n);
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
    switch (lit_value(solver, l)) {
    case BVAL_FALSE:
      break;
    case BVAL_UNDEF_FALSE :
    case BVAL_UNDEF_TRUE :
      lit[j] = l;
      j++;
      break;
    default: // true literal, so the clause is true
      return;
    }
  }
  n = j; // new clause size

  nsat_solver_add_clause(solver, n, lit);
}



/**********************************
 *  ADDITION OF LEARNED CLAUSES   *
 *********************************/

/*
 * Rescale the activity of all the learned clauses.
 * (divide all the activities by CLAUSE_ACTIVITY_THRESHOLD).
 */
static void rescale_clause_activities(sat_solver_t *solver) {
  cidx_t cidx, end;

  end = solver->pool.size;
  cidx = clause_pool_first_learned_clause(&solver->pool);
  while (cidx < end) {
    multiply_learned_clause_activity(&solver->pool, cidx, INV_CLAUSE_ACTIVITY_THRESHOLD);
    cidx = clause_pool_next_clause(&solver->pool, cidx);
  }
  solver->cla_inc *= INV_CLAUSE_ACTIVITY_THRESHOLD;
}


/*
 * Increase the activity of a learned clause.
 * - cidx = its index
 */
static void increase_clause_activity(sat_solver_t *solver, cidx_t cidx) {
  increase_learned_clause_activity(&solver->pool, cidx, solver->cla_inc);
  if (get_learned_clause_activity(&solver->pool, cidx) > CLAUSE_ACTIVITY_THRESHOLD) {
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
static cidx_t add_learned_clause(sat_solver_t *solver, uint32_t n, const literal_t *lit) {
  cidx_t cidx;
  
  assert(n > 2);

  cidx = clause_pool_add_learned_clause(&solver->pool, n, lit);
  set_learned_clause_activity(&solver->pool, cidx, solver->cla_inc);
  add_clause_watch(solver, lit[0], cidx);
  add_clause_watch(solver, lit[1], cidx);

  return cidx;
}


/*********************************
 *  DELETION OF LEARNED CLAUSES  *
 ********************************/

// TBD


/********************************************
 *  SIMPLIFICATION OF THE CLAUSE DATABASE   *
 *******************************************/

// TBD


/*************************
 *  LITERAL ASSIGNMENT   *
 ***********************/

// TBD


/**************************
 *  BOOLEAN PROPAGATION   *
 *************************/

// TBD


/*******************************************************
 *  CONFLICT ANALYSIS AND CREATION OF LEARNED CLAUSES  *
 ******************************************************/

// TBD


/*****************************
 *  MAIN SOLVING PROCEDURES  *
 ****************************/

// TBD


/************
 *  MODELS  *
 ***********/

/*
 * Return the model: copy all variable value into val
 * - val's size must be at least solver->nvars
 * - val[0] is always true
 */
void nsat_get_allvars_assignment(sat_solver_t *solver, bval_t *val) {
  uint32_t i, n;

  n = solver->nvars;
  for (i=0; i<n; i++) {
    val[i] = solver->value[i];
  }
}


/*
 * Copy all true literals in array a:
 * - a must have size >= solver->nvars.
 * return the number of literals added to a.
 */
uint32_t get_true_literals(sat_solver_t *solver, literal_t *a) {
  uint32_t n;
  literal_t l;

  n = 0;
  for (l = 0; l< solver->nliterals; l++) {
    if (lit_value(solver, l) == BVAL_TRUE) {
      a[n] = l;
      n ++;
    }
  }

  return n;
}





/**********
 *  JUNK  *
 *********/

/*
 * Fake functions for testing
 */
void test(sat_solver_t *solver) {
  literal_t aux[4];

  aux[0] = pos(1);
  aux[1] = neg(2);
  aux[2] = pos(3);
  aux[3] = neg(4);

  add_learned_clause(solver, 4, aux);
}

float test0(sat_solver_t *solver, cidx_t cidx) {
  return get_learned_clause_activity(&solver->pool, cidx);
}

void test1(sat_solver_t *solver, cidx_t cidx, float b) {
  increase_learned_clause_activity(&solver->pool, cidx, b);
}

void test2(sat_solver_t *solver, cidx_t cidx, float b) {
  multiply_learned_clause_activity(&solver->pool, cidx, b);
}

void test3(sat_solver_t *solver, cidx_t cidx, float b) {
  set_learned_clause_activity(&solver->pool, cidx, b);
}

float test0a(sat_solver_t *solver, cidx_t cidx) {
  clause_t *aux;

  aux = clause_of_idx(&solver->pool, cidx);
  return aux->aux.f;
}

void test1a(sat_solver_t *solver, cidx_t cidx, float b) {
  clause_t *aux;

  aux = clause_of_idx(&solver->pool, cidx);
  aux->aux.f += b;
}

void test2a(sat_solver_t *solver, cidx_t cidx, float b) {
  clause_t *aux;

  aux = clause_of_idx(&solver->pool, cidx);
  aux->aux.f *= b;
}

void test3a(sat_solver_t *solver, cidx_t cidx, float b) {
  clause_t *aux;

  aux = clause_of_idx(&solver->pool, cidx);
  aux->aux.f = b;
}




/****************************************
 *   CONSISTENCY CHECKS FOR DEBUGGING   *
 ***************************************/

#if DEBUG

/*
 * Check whether the clause pool counters are correct.
 */
static bool good_counters(const clause_pool_t *pool) {
  uint32_t prob_clauses, prob_lits, learned_clauses, learned_lits, i;

  prob_clauses = 0;
  prob_lits = 0;
  learned_clauses = 0;
  learned_lits = 0;

  i = clause_pool_first_clause(pool);
  while (i < pool->learned) {
    prob_clauses ++;
    prob_lits += clause_length(pool, i);
    i = clause_pool_next_clause(pool, i);
  }
  while (i < pool->size) {
    learned_clauses ++;
    learned_lits += clause_length(pool, i);
    i = clause_pool_next_clause(pool, i);
  }

  return 
    prob_clauses == pool->num_prob_clauses &&
    prob_lits == pool->num_prob_literals &&
    learned_clauses == pool->num_learned_clauses &&
    learned_lits == pool->num_learned_literals;
}

static void clause_pool_check_counters(const clause_pool_t *pool) {
  if (!good_counters(pool)) {
    fprintf(stderr, "**** BUG: inconsistent pool counters ****\n");
    fflush(stderr);
  }
}


/*
 * HEAP INVARIANTS
 */
static void check_heap(var_heap_t *heap) {
  uint32_t i, j, n;
  bvar_t x;

  n = heap->heap_last;
  for (i=0; i<=n; i++) {
    x = heap->heap[i];
    if (heap->heap_index[x] != i) {
      fprintf(stderr, "*** BUG: heap[%"PRIu32"] = %"PRIu32" but heap_index[%"PRIu32"] = %"PRIu32" ****\n",
	      i, x, x, heap->heap_index[x]);
    }
    j = i>>1; // parent of i (or j=i=0 for the special marker)
    if (heap->activity[j] < heap->activity[i]) {
      fprintf(stderr, "*** BUG: bad heap ordering: activity[%"PRIu32"] < activity[%"PRIu32"] ****\n", j, i);
    }
  }

  n = heap->size;
  for (i=0; i<n; i++) {
    j = heap->heap_index[i];
    if (j >= 0 && heap->heap[j] != i) {
      fprintf(stderr, "*** BUG: heap_index[%"PRIu32"] = %"PRIu32" but heap[%"PRIu32"] = %"PRIu32" ****\n",
	      i, j, j, heap->heap[j]);
    }
  }
}

#endif
