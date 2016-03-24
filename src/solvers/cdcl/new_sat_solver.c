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
#include "utils/memalloc.h"
#include "utils/uint_array_sort.h"
#include "utils/uint_array_sort2.h"


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
 * The following functions check internal consistency. They are defined
 * at the end of this file. They print an error on stderr if the checks fail.
 */
static void check_clause_pool_counters(const clause_pool_t *pool);
static void check_clause_pool_learned_index(const clause_pool_t *pool);
static void check_heap(const var_heap_t *heap);
static void check_candidate_clauses_to_delete(const sat_solver_t *solver, const cidx_t *a, uint32_t n);
static void check_watch_vectors(const sat_solver_t *solver);
static void check_propagation(const sat_solver_t *solver);
static void check_marks(const sat_solver_t *solver);
static void check_all_unmarked(const sat_solver_t *solver);

#else

/*
 * Placeholders: do nothing
 */
static inline void check_clause_pool_counters(const clause_pool_t *pool) { }
static inline void check_clause_pool_learned_index(const clause_pool_t *pool) { }
static inline void check_heap(const var_heap_t *heap) { }
static inline void check_candidate_clauses_to_delete(const sat_solver_t *solver, const cidx_t *a, uint32_t n) { }
static inline void check_watch_vectors(const sat_solver_t *solver) { }
static inline void check_propagation(const sat_solver_t *solver) { }
static inline void check_marks(const sat_solver_t *solver) { }
static inline void check_all_unmarked(const sat_solver_t *solver) {}

#endif


/*
 * Crude implementation: get statistics on every conflict
 */
#define CONFLICT_STATS 0

#if CONFLICT_STATS

static FILE *stat_file = NULL;

static void open_stat_file(void) {
  stat_file = fopen("conflict_stats.txt", "w");
}

static void close_stat_file(void) {
  if (stat_file != NULL) {
    fclose(stat_file);
  }
}

static void export_conflict_stat(uint32_t ldb, uint32_t clevel, uint32_t blevel, uint64_t slow_ema, uint64_t fast_ema, uint64_t blocking_ema) {
  double slow, fast, blocking;

  if (stat_file != NULL) {
    slow = (double)slow_ema/4.3e9;
    fast = (double)fast_ema/4.3e9;
    blocking = (double)blocking_ema/4.3e9;
    fprintf(stat_file, "%"PRIu32",%"PRIu32",%"PRIu32",%f,%f,%f\n", ldb, clevel, blevel, slow, fast, blocking); 
  }
}


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


/*********************
 *  LITERAL BUFFER   *
 ********************/

/*
 * Capacity increase for literal buffers:
 * - about 50% increase rounded up to a multiple of four
 */
static inline uint32_t lbuffer_cap_increase(uint32_t cap) {
  return ((cap >> 1) + 8) & ~3;
}

/*
 * Initialize
 */
static void init_lbuffer(lbuffer_t *b) {
  uint32_t n;

  n = DEF_LBUFFER_SIZE;
  assert(n <= MAX_LBUFFER_SIZE);
  b->data = (literal_t *) safe_malloc(n * sizeof(literal_t));
  b->capacity = n;
  b->size = 0;
}

/*
 * Make it larger.
 */
static void extend_lbuffer(lbuffer_t *b) {
  uint32_t n;

  n = b->capacity + lbuffer_cap_increase(b->capacity);
  assert(n > b->capacity);
  if (n > MAX_LBUFFER_SIZE) {
    out_of_memory();
  }
  b->data = (literal_t *) safe_realloc(b->data, n * sizeof(literal_t));
  b->capacity = n;
}

/*
 * Add literal l at the end of buffer b
 */
static void lbuffer_push(lbuffer_t *b, literal_t l) {
  uint32_t i;

  i = b->size;
  if (i == b->capacity) {
    extend_lbuffer(b);
  }
  assert(i < b->capacity);
  b->data[i] = l;
  b->size = i+1;
}

/*
 * Reset: empty the buffer
 */
static inline void reset_lbuffer(lbuffer_t *b) {
  b->size = 0;
}

/*
 * Reset and make room for one literal
 */
static inline void lbuffer_reset_and_reserve(lbuffer_t *b) {
  assert(b->capacity >= 1);
  b->size = 1;
}

/*
 * Free memory
 */
static void delete_lbuffer(lbuffer_t *b) {
  safe_free(b->data);
  b->data = NULL;
}



/******************
 * LITERAL QUEUE  *
 *****************/

/*
 * Capacity increase: same as for lbuffer
 */
static inline uint32_t lqueue_cap_increase(uint32_t cap) {
  return ((cap >> 1) + 8) & ~3;
}

/*
 * Initialize
 */
static void init_lqueue(lqueue_t *q) {
  uint32_t n;

  n = DEF_LQUEUE_SIZE;
  assert(n <= MAX_LQUEUE_SIZE);
  q->data = (literal_t *) safe_malloc(n * sizeof(literal_t));
  q->capacity = n;
  q->head = 0;
  q->tail = 0;
}

/*
 * Make the queue bigger
 */
static void extend_lqueue(lqueue_t *q) {
  uint32_t n;

  n = q->capacity + lqueue_cap_increase(q->capacity);
  assert(n > q->capacity);
  if (n > MAX_LQUEUE_SIZE) {
    out_of_memory();
  }
  q->data = (literal_t *) safe_realloc(q->data, n * sizeof(literal_t));
  q->capacity = n;
}

/*
 * Add l at the end of the queue
 */
static void lqueue_push(lqueue_t *q, literal_t l) {
  uint32_t i, n, j;

  i = q->tail;
  q->data[i] = l;
  i++;
  if (i == q->capacity) {
    i = 0;
  }
  q->tail = i;

  if (i == q->head) {
    /*
     * full queue in q->data[0 ... i-1] + q->data[head .. cap-1].
     * make the array bigger 
     * if i>0, shift data[head ... cap - 1] to the end of the new array.
     */
    n = q->capacity;    // cap before increase
    extend_lqueue(q);
    if (i == 0) {
      q->tail = n;
    } else {
      j = q->capacity;
      do {
	n --;
	j --;
	q->data[j] = q->data[n];
      } while (n > i);
      q->head = j;
    }
  }
}


/*
 * Check emptiness
 */
static inline bool lqueue_is_empty(lqueue_t *q) {
  return q->head == q->tail;
}


/*
 * Remove the first element and return it.
 * - the queue must not be empty
 */
static literal_t lqueue_pop(lqueue_t *q) {
  literal_t l;
  uint32_t i;

  assert(! lqueue_is_empty(q));

  i = q->head;
  l = q->data[i];
  i ++;
  q->head = (i < q->capacity) ? i : 0;

  return l;
}


/*
 * Empty the queue
 */
static inline void reset_lqueue(lqueue_t *q) {
  q->head = 0;
  q->tail = 0;
}


/*
 * Delete
 */
static void delete_lqueue(lqueue_t *q) {
  safe_free(q->data);
  q->data = NULL;
}



/*********************************
 *  STACK FOR IMPLICATION GRAPH  *
 ********************************/

/*
 * Initialize the stack. Nothing allocated yet.
 */
static void init_gstack(gstack_t *gstack) {
  gstack->data = NULL;
  gstack->top = 0;
  gstack->size = 0;
}

/*
 * Increment in size: 50% of the current size, rounded up to a multiple of 2.
 */
static inline uint32_t gstack_size_increase(uint32_t n) {
  return ((n>>1) + 3) & ~1;
}

/*
 * Make the stack larger
 */
static void extend_gstack(gstack_t *gstack) {
  uint32_t n;

  n = gstack->size;
  if (n == 0) {
    // first allocation
    n = DEF_GSTACK_SIZE;
    assert(n <= MAX_GSTACK_SIZE);
    gstack->data = (gstack_elem_t *) safe_malloc(n * sizeof(gstack_elem_t));
    gstack->size = n;
  } else {
    // increase size by 50%, rounded to a multiple of 2
    n += gstack_size_increase(n);
    if (n > MAX_GSTACK_SIZE) {
      out_of_memory();
    }
    gstack->data = (gstack_elem_t *) safe_realloc(gstack->data, n * sizeof(gstack_elem_t));
    gstack->size = n;
  }
}

/*
 * Delete the stack
 */
static void delete_gstack(gstack_t *gstack) {
  safe_free(gstack->data);
  gstack->data = NULL;
}

/*
 * Push pair (x, n) on the stack
 */
static void gstack_push_var(gstack_t *gstack, bvar_t x, uint32_t n) {
  uint32_t i;

  i = gstack->top;
  if (i == gstack->size) {
    extend_gstack(gstack);
  }
  assert(i < gstack->size);
  gstack->data[i].var = x;
  gstack->data[i].index = n;
  gstack->top = i+1;
}

/*
 * Check emptiness
 */
static inline bool gstack_is_empty(gstack_t *gstack) {
  return gstack->top == 0;
}

/*
 * Get top element
 */
static inline gstack_elem_t *gstack_top(gstack_t *gstack) {
  assert(gstack->top > 0);
  return gstack->data + (gstack->top - 1);
}

/*
 * Remove the top element
 */
static inline void gstack_pop(gstack_t *gstack) {
  assert(gstack->top > 0);
  gstack->top --;
}

/*
 * Empty the stack
 */
static inline void reset_gstack(gstack_t *gstack) {
  gstack->top = 0;
}






/******************
 *  CLAUSE POOL   *
 *****************/

/*
 * Capacity increase:
 * cap += ((cap >> 1) + (cap >> 6) + (cap >> 7) + 2048) & ~3
 *
 * Since the initial capacity is 262144, we get an increasing
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

static bool clause_pool_invariant(const clause_pool_t *pool) {
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
  pool->data = (uint32_t *) safe_malloc(DEF_CLAUSE_POOL_CAPACITY * sizeof(uint32_t));
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
  safe_free(pool->data);
  pool->data = NULL;
}

static void reset_clause_pool(clause_pool_t *pool) {
  assert(clause_pool_invariant(pool));

  if (pool->capacity > RESET_CLAUSE_POOL_CAPACITY) {
    safe_free(pool->data);
    pool->data = (uint32_t *) safe_malloc(RESET_CLAUSE_POOL_CAPACITY * sizeof(uint32_t));
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

  pool->data = (uint32_t *) safe_realloc(pool->data, cap * sizeof(uint32_t));;
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
 * CLAUSE ADDITION
 */

/*
 * Initialize the clause that starts at index cidx:
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

  return cidx;
}


/*
 * ACCESS CLAUSES
 */
#ifndef NDEBUG
static inline bool good_clause_idx(const clause_pool_t *pool, cidx_t idx) {
  return ((idx & 3) == 0) && idx < pool->size;
}
#endif

static inline bool is_learned_clause_idx(const clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return  idx >= pool->learned;
}

static inline bool is_problem_clause_idx(const clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return  idx < pool->learned;  
}

static inline clause_t *clause_of_idx(const clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return (clause_t *) ((char *) (pool->data + idx));
}

static inline uint32_t clause_length(const clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return pool->data[idx];
}

/*
 * Start of the literal array for clause idx
 */
static inline literal_t *clause_literals(const clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return pool->data + idx + 2;
}

/*
 * Full size of a clause of n literals:
 * - 2 + n, rounded up to the next multiple of four
 */
static inline uint32_t full_length(uint32_t n) {
  return (n + 5) & ~3;
}

static inline uint32_t clause_full_length(const clause_pool_t *pool, uint32_t i) {
  assert(good_clause_idx(pool, i));
  return full_length(pool->data[i]);
}


/*
 * Get watch literals of clause cidx
 * - the first literal is the implied literal if any
 */
static inline literal_t first_literal_of_clause(const clause_pool_t *pool, cidx_t cidx) {
  assert(good_clause_idx(pool, cidx));
  return pool->data[cidx + 2];
}

static inline literal_t second_literal_of_clause(const clause_pool_t *pool, cidx_t cidx) {
  assert(good_clause_idx(pool, cidx));
  return pool->data[cidx + 3];
}


/*
 * CLAUSE ACTIVITY
 */
static inline void set_learned_clause_activity(clause_pool_t *pool, cidx_t cidx, float act) {
  clause_t *c;

  assert(is_learned_clause_idx(pool, cidx) && sizeof(float) == sizeof(uint32_t));

  c = clause_of_idx(pool, cidx);
  c->aux.f = act;
}

static inline float get_learned_clause_activity(const clause_pool_t *pool, cidx_t cidx) {
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

static inline void multiply_learned_clause_activity(clause_pool_t *pool, cidx_t cidx, float scale) {
  clause_t *c;

  assert(is_learned_clause_idx(pool, cidx) && sizeof(float) == sizeof(uint32_t));

  c = clause_of_idx(pool, cidx);
  c->aux.f *= scale;
}


/*
 * PADDING BLOCKS
 */

/*
 * Check whether i is the start of a padding block
 */
static inline bool is_padding_start(const clause_pool_t *pool, uint32_t i) {
  assert(i < pool->size && is_multiple_of_four(i));
  return pool->data[i] == 0;
}

/*
 * Check whehter is is the start of a clause
 */
static inline bool is_clause_start(const clause_pool_t *pool, uint32_t i) {
  return !is_padding_start(pool, i);
}

/*
 * Length of the padding block that starts at index i
 */
static inline uint32_t padding_length(const clause_pool_t *pool, uint32_t i) {
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
    pool->available += n;
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

  assert(clause_pool_invariant(pool));
}


/*
 * DELETE CLAUSES
 */

/*
 * Delete the clause that start at index idx
 */
static void clause_pool_delete_clause(clause_pool_t *pool, cidx_t idx) {
  uint32_t n;

  assert(good_clause_idx(pool, idx));

  n = pool->data[idx]; // clause length

  // update the statistics: we must do this first because
  // padding may reduce pool->size.
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

  clause_pool_padding(pool, idx, full_length(n));
}


/*
 * Shrink clause idx: n = new size
 */
static void clause_pool_shrink_clause(clause_pool_t *pool, cidx_t idx, uint32_t n) {
  uint32_t old_n, old_len, new_len;

  assert(good_clause_idx(pool, idx) && n >= 2 && n <= clause_length(pool, idx));

  old_n = clause_length(pool, idx);
  old_len = full_length(old_n);
  new_len = full_length(n);

  if (is_problem_clause_idx(pool, idx)) {
    assert(pool->num_prob_clauses > 0);
    assert(pool->num_prob_literals >= old_n);
    pool->num_prob_literals -= (old_n - n);
  } else {
    assert(pool->num_learned_clauses > 0);
    assert(pool->num_learned_literals >= old_n);
    pool->num_learned_literals -= (old_n - n);
  }

  assert(new_len <= old_len);
  if (new_len < old_len) {
    clause_pool_padding(pool, idx + new_len, old_len - new_len);
  }

  pool->data[idx] = n;
}


/*
 * SCAN THE SET OF CLAUSES
 */

/*
 * Find the next clause, scanning from index i
 * - i may be the start of a clause or a padding block
 * - if there's no more clause after i then we return pool->size
 */
static cidx_t next_clause_index(const clause_pool_t *pool, cidx_t i) {
  while (i < pool->size && is_padding_start(pool, i)) {
    i += padding_length(pool, i);
  }
  return i;
}

static inline cidx_t clause_pool_first_clause(const clause_pool_t *pool) {
  return next_clause_index(pool, 0);
}

static inline cidx_t clause_pool_first_learned_clause(const clause_pool_t *pool) {
  return next_clause_index(pool, pool->learned);
}

/*
 * Clause that follows idx:
 * - idx may be either the start of a padding block, or the start of a clause,
 *   or the end mark (pool->size)
 */
static cidx_t clause_pool_next_clause(const clause_pool_t *pool, cidx_t idx) {
  uint32_t n;

  assert(idx <= pool->size);

  if (idx == pool->size) {
    return idx;
  } 
  
  n = 0;
  if (is_clause_start(pool, idx)) {
    n = clause_full_length(pool, idx);
  }
  return next_clause_index(pool, idx + n);
}





/*****************
 *  WATCH LISTS  *
 ****************/

/*
 * Initial capacity: smallish.
 *
 * We set MAX_WATCH_CAPACITY to ensure two properties:
 * 1) (MAX + watch_cap_increase(MAX)) doesn't overflow for uint32_t.
 * 2) (sizeof(watch_t) + MAX * sizeof(unit32_t)) doesn't overflow for size_t.
 *
 * For condition 1, we need MAX <= 0xAAAAAAA7 = 2863311527.
 * For condition 2, we need MAX <= (SIZE_MAX/4) - 2.
 */
#define DEF_WATCH_CAPACITY 6

#if ((SIZE_MAX/4) - 2) < 2863311527
#define MAX_WATCH_CAPACITY ((uint32_t) ((SIZE_MAX/4) - 2))
#else
#define MAX_WATCH_CAPACITY ((uint32_t) 2863311527)
#endif


/*
 * Capacity increase for watch vectors:
 * - about 50% increase, rounded up to force the increment to be a multiple of four
 */
static inline uint32_t watch_cap_increase(uint32_t cap) {
  return ((cap >> 1) + 8) & ~3;
}

/*
 * Allocate/extend vector *w:
 * - this makes sure there's room for one more element
 */
static void resize_watch(watch_t **w) {
  watch_t *v;
  uint32_t i, n;
  
  v = *w;
  if (v == NULL) {
    n = DEF_WATCH_CAPACITY;
    v = (watch_t *) safe_malloc(sizeof(watch_t) + n * sizeof(uint32_t));
    v->capacity = n;
    v->size = 0;
    assert(n >= 1);
    *w = v;
  } else {
    i = v->size;
    n = v->capacity;
    if (i >= n) {
      n += watch_cap_increase(n);
      if (n > MAX_WATCH_CAPACITY) {
	out_of_memory();
      }
      v = (watch_t *) safe_realloc(v, sizeof(watch_t) + n * sizeof(uint32_t));
      v->capacity = n;
      assert(i < n);
      *w = v;
    }
  }
}


/*
 * Make v smaller if possible.
 * - v must not be NULL
 */
static watch_t *shrink_watch(watch_t *v) {
  uint32_t n, cap;

  assert(v != NULL && v->size <= v->capacity && v->capacity <= MAX_WATCH_CAPACITY);

  n = v->size;

  // search for the minimal capacity >= v->size
  // since n <= MAX_WATCH_CAPACITY, there's no risk of numerical overflow
  cap = DEF_WATCH_CAPACITY;
  while (cap < n) {
    cap += watch_cap_increase(cap);
  }

  if (cap < v->capacity) {
    v = (watch_t *) safe_realloc(v, sizeof(watch_t) + cap * sizeof(uint32_t));
    v->capacity = cap;
    assert(v->size <= v->capacity);   
  }

  return v;
}


/*
 * Add k at the end of vector *w.
 * - if *w is NULL, allocate a vector of default size
 * - if *w if full, make it 50% larger.
 */
static void add_watch(watch_t **w, uint32_t k) {
  watch_t *v;
  uint32_t i;

  resize_watch(w);
  v = *w;
  i = v->size;
  assert(i < v->capacity);
  v->data[i] = k;
  v->size = i+1;
}

/*
 * Add two elements k1 and k2 at the end of vector *w
 */
static void add_watch2(watch_t **w, uint32_t k1, uint32_t k2) {
  add_watch(w, k1);
  add_watch(w, k2);
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
 * Extend the stack: nvar = new size
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
  safe_free(s->lit);
  safe_free(s->level_index);
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

  heap->activity = (double *) safe_malloc(n * sizeof(double));
  heap->heap_index = (int32_t *) safe_malloc(n * sizeof(int32_t));
  heap->heap = (bvar_t *) safe_malloc(n * sizeof(bvar_t));

  // marker
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
 * Extend the heap to n variables
 */
static void extend_heap(var_heap_t *heap, uint32_t n) {
  uint32_t old_size, i;

  old_size = heap->size;
  assert(old_size < n);
  heap->activity = (double *) safe_realloc(heap->activity, n * sizeof(double));
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
  safe_free(heap->activity);
  safe_free(heap->heap_index);
  safe_free(heap->heap);
  heap->activity = NULL;
  heap->heap_index = NULL;
  heap->heap = NULL;
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
  az = act[z];   // activity of the last element

  i = 1;      // root
  j = 2;      // left child of i
  while (j < last) {
    /*
     * find child of i with highest activity.
     */
    x = h[j];
    ax = act[x];
    if (j+1 < last) {
      y = h[j+1];
      ay = act[y];
      if (ay > ax) {
	j++;
	x = y;
	ax = ay;
      }
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
 * Get and remove the top element
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
 */
static void rescale_var_activities(var_heap_t *heap) {
  uint32_t i, n;
  double *act;

  n = heap->size;
  act = heap->activity;
  for (i=1; i<n; i++) {
    act[i] *= INV_VAR_ACTIVITY_THRESHOLD;
  }
  heap->act_increment *= INV_VAR_ACTIVITY_THRESHOLD;
}

/*
 * Increase the activity of variable x
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
  stat->decisions = 0;
  stat->random_decisions = 0;
  stat->propagations = 0;
  stat->conflicts = 0;
  stat->prob_clauses_deleted = 0;
  stat->learned_clauses_deleted = 0;
  stat->subsumed_literals = 0;
  stat->starts = 0;
  stat->simplify_calls = 0;
  stat->reduce_calls = 0;
  stat->pp_pure_lits = 0;
  stat->pp_unit_lits = 0;
  stat->pp_clauses_deleted = 0;
}


/*
 * Initialization:
 * - sz = initial size of the variable-indexed arrays.
 * - pp = flag to enable preprocessing
 *
 * - if sz is zero, the default size is used.
 * - the solver is initialized with one variable (the reserved variable 0).
 */
void init_nsat_solver(sat_solver_t *solver, uint32_t sz, bool pp) {
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
  solver->preprocess = pp;

  solver->verbosity = 0;

  solver->nvars = 1;
  solver->nliterals = 2;
  solver->vsize = n;
  solver->lsize = 2 * n;

  solver->value = (uint8_t *) safe_malloc(n * 2 * sizeof(uint8_t));
  solver->ante_tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  solver->ante_data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  solver->level = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  solver->watch = (watch_t **) safe_malloc(n * 2 * sizeof(watch_t *));

  solver->occ = NULL;
  if (solver->preprocess) {
    solver->occ = (uint32_t *) safe_malloc(n * 2 * sizeof(uint32_t)); // one counter per literal
    solver->occ[0] = 0;  // for literal 0 = true
    solver->occ[1] = 0;  // for literal 1 = false
  }

  // variable 0: true
  solver->value[0] = BVAL_TRUE;
  solver->value[1] = BVAL_FALSE;
  solver->ante_tag[0] = ATAG_UNIT;
  solver->ante_data[0] = 0;
  solver->level[0] = 0;
  solver->watch[0] = NULL;
  solver->watch[1] = NULL;

  init_heap(&solver->heap, n);
  init_stack(&solver->stack, n);

  solver->has_empty_clause = false;
  solver->units = 0;
  solver->binaries = 0;
  init_clause_pool(&solver->pool);

  solver->conflict_tag = CTAG_NONE;

  solver->prng = PRNG_SEED;
  solver->randomness = (uint32_t) (VAR_RANDOM_FACTOR * VAR_RANDOM_SCALE);
  solver->cla_inc = INIT_CLAUSE_ACTIVITY_INCREMENT;
  solver->inv_cla_decay = ((float) 1)/CLAUSE_DECAY_FACTOR;

  solver->keep_lbd = 6;

  init_stats(&solver->stats);

  solver->cidx_array = NULL;

  init_lbuffer(&solver->buffer);
  init_lbuffer(&solver->aux);
  init_gstack(&solver->gstack);
  init_tag_map(&solver->map, 0); // use default size

  init_lqueue(&solver->queue);
}


/*
 * Set the prng seed
 */
void nsat_solver_set_seed(sat_solver_t *solver, uint32_t seed) {
  solver->prng = seed;
}

/*
 * Set the verbosity level
 */
void nsat_solver_set_verbosity(sat_solver_t *solver, uint32_t level) {
  solver->verbosity = level;
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

  if (solver->preprocess) {
    safe_free(solver->occ);
  }

  solver->value = NULL;
  solver->ante_tag = NULL;
  solver->ante_data = NULL;
  solver->level = NULL;
  solver->watch = NULL;

  delete_heap(&solver->heap);
  delete_stack(&solver->stack);
  delete_clause_pool(&solver->pool);

  safe_free(solver->cidx_array);
  solver->cidx_array = NULL;

  delete_lbuffer(&solver->buffer);
  delete_lbuffer(&solver->aux);
  delete_gstack(&solver->gstack);
  delete_tag_map(&solver->map);

  delete_lqueue(&solver->queue);
}


/*
 * Reset: remove all variables and clauses
 * - reset heuristics parameters
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

  solver->conflict_tag = CTAG_NONE;

  solver->prng = PRNG_SEED;
  solver->randomness = (uint32_t) (VAR_RANDOM_FACTOR * VAR_RANDOM_SCALE);
  solver->cla_inc = INIT_CLAUSE_ACTIVITY_INCREMENT;
  solver->inv_cla_decay = ((float) 1)/CLAUSE_DECAY_FACTOR;

  init_stats(&solver->stats);

  safe_free(solver->cidx_array);
  solver->cidx_array = NULL;

  reset_lbuffer(&solver->buffer);
  reset_lbuffer(&solver->aux);
  reset_gstack(&solver->gstack);
  clear_tag_map(&solver->map);

  reset_lqueue(&solver->queue);
}



/**************************
 *  HEURISTIC PARAMETERS  *
 *************************/

/*
 * Variable activity decay: must be between 0 and 1.0
 * - smaller number means faster decay
 */
void nsat_set_var_decay_factor(sat_solver_t *solver, double factor) {
  assert(0.0 < factor && factor < 1.0);
  solver->heap.inv_act_decay = 1/factor;
}

/*
 * Clause activity decay: must be between 0 and 1.0
 * - smaller means faster decay
 */
void nsat_set_clause_decay_factor(sat_solver_t *solver, float factor) {
  assert(0.0F < factor && factor < 1.0F);
  solver->inv_cla_decay = 1/factor;
}

/*
 * Randomness: the paramenter is approximately the ratio of random
 * decisions.
 * - randomness = 0: no random decisions
 * - randomness = 1.0: all decicsions are random
 */
void nsat_set_randomness(sat_solver_t *solver, float randomness) {
  assert(0.0F <= randomness && randomness <= 1.0F);
  solver->randomness = (uint32_t)(randomness * VAR_RANDOM_SCALE);
}

/*
 * Set the prng seed
 */
void nsat_set_random_seed(sat_solver_t *solver, uint32_t seed) {
  solver->prng = seed;
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

  solver->value = (uint8_t *) safe_realloc(solver->value, new_size * 2 * sizeof(uint8_t));
  solver->ante_tag = (uint8_t *) safe_realloc(solver->ante_tag, new_size * sizeof(uint8_t));
  solver->ante_data = (uint32_t *) safe_realloc(solver->ante_data, new_size * sizeof(uint32_t));
  solver->level = (uint32_t *) safe_realloc(solver->level, new_size * sizeof(uint32_t));
  solver->watch = (watch_t **) safe_realloc(solver->watch, new_size * 2 * sizeof(watch_t *));

  if (solver->preprocess) {
    solver->occ = (uint32_t *) safe_realloc(solver->occ, new_size * 2 * sizeof(uint32_t));
  }

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

  for (i=solver->nvars; i<nv; i++) {
    solver->value[pos(i)] = BVAL_UNDEF_FALSE;
    solver->value[neg(i)] = BVAL_UNDEF_TRUE;
    solver->ante_tag[i] = ATAG_NONE;
    solver->ante_data[i] = 0;
    solver->level[i] = UINT32_MAX;
    solver->watch[pos(i)] = NULL;
    solver->watch[neg(i)] = NULL;
  }

  if (solver->preprocess) {
    for (i=solver->nvars; i<nv; i++) {
      solver->occ[pos(i)] = 0;
      solver->occ[neg(i)] = 0;
    }
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
 * Converse: extract literal from index k
 */
static inline literal_t idx2lit(uint32_t k) {
  assert((k & 1) == 1);
  return k >> 1;
}

/*
 * Check whether k is a clause index: low-order bit is 0
 */
static inline bool idx_is_clause(uint32_t k) {
  return (k & 1) == 0;
}

/*
 * Check whether k is a literal index: low-order bit is 1
 */
static inline bool idx_is_literal(uint32_t k) {
  return (k & 1) == 1;
}

/*
 * Add clause index in the watch vector for literal l
 * - l1 = blocker
 */
static inline void add_clause_watch(sat_solver_t *solver, literal_t l, cidx_t cidx, literal_t l1) {
  assert(l < solver->nliterals && l1 < solver->nliterals);
  add_watch2(solver->watch + l, cidx, l1);
}

/*
 * Add literal l1 in the watch vector for l
 */
static inline void add_literal_watch(sat_solver_t *solver, literal_t l, literal_t l1) {
  assert(l < solver->nliterals);
  add_watch(solver->watch + l, lit2idx(l1));
}


/*
 * All clause index cidx in the watch vectors of literals lit[0 ... n-1]
 */
static void add_clause_all_watch(sat_solver_t *solver, uint32_t n, const literal_t *lit, cidx_t cidx) {
  uint32_t i;
  literal_t l;

  for (i=0; i<n; i++) {
    l = lit[i];
    assert(l < solver->nliterals);
    add_watch(solver->watch + l, cidx);
  }
}


/*************************
 *  LITERAL ASSIGNMENT   *
 ***********************/

/*
 * Assign literal l at base level
 */
static void assign_literal(sat_solver_t *solver, literal_t l) {
  bvar_t v;

#if TRACE
  printf("---> Assigning literal %"PRIu32"\n", l);
  fflush(stdout);
#endif

  assert(l < solver->nliterals);
  assert(lit_is_unassigned(solver, l));
  assert(solver->decision_level == 0);

  push_literal(&solver->stack, l);

  solver->value[l] = BVAL_TRUE;
  solver->value[not(l)] = BVAL_FALSE;

  v = var_of(not(l));
  // value of v = BVAL_TRUE if l = pos(v) or BVAL_FALSE if l = neg(v)
  //  solver->value[v] = BVAL_TRUE ^ sign_of(l);
  solver->ante_tag[v] = ATAG_UNIT;
  solver->ante_data[v] = 0;
  solver->level[v] = 0;

  assert(lit_is_true(solver, l));
}


/*
 * Decide literal: increase decision level then
 * assign literal l to true and push it on the stack
 */
static void nsat_decide_literal(sat_solver_t *solver, literal_t l) {
  uint32_t k;
  bvar_t v;

  assert(l < solver->nliterals);
  assert(lit_is_unassigned(solver, l));

  solver->stats.decisions ++;

  // Increase decision level
  k = solver->decision_level + 1;
  solver->decision_level = k;
  if (solver->stack.nlevels <= k) {
    increase_stack_levels(&solver->stack);
  }
  solver->stack.level_index[k] = solver->stack.top;

  push_literal(&solver->stack, l);

  solver->value[l] = BVAL_TRUE;
  solver->value[not(l)] = BVAL_FALSE;

  v = var_of(not(l));
  solver->ante_tag[v] = ATAG_DECISION;
  solver->ante_data[v] = 0; // not used
  solver->level[v] = k;

  assert(lit_is_true(solver, l));

#if TRACE
  printf("\n---> DPLL:   Decision: literal %"PRIu32", decision level = %"PRIu32"\n", l, k);
  fflush(stdout);
#endif
}


/*
 * Propagated literal: tag = antecedent tag, data = antedecent data
 */
static void implied_literal(sat_solver_t *solver, literal_t l, antecedent_tag_t tag, uint32_t data) {
  bvar_t v;

  assert(l < solver->nliterals);
  assert(lit_is_unassigned(solver, l));

  solver->stats.propagations ++;

  push_literal(&solver->stack, l);

  solver->value[l] = BVAL_TRUE;
  solver->value[not(l)] = BVAL_FALSE;

  v = var_of(not(l));
  solver->ante_tag[v] = tag;
  solver->ante_data[v] = data;
  solver->level[v] = solver->decision_level;

  assert(lit_is_true(solver, l));
}


/*
 * Literal l implied by clause cidx
 */
static void clause_propagation(sat_solver_t *solver, literal_t l, cidx_t cidx) {
  assert(good_clause_idx(&solver->pool, cidx));

  implied_literal(solver, l, ATAG_CLAUSE, cidx);

#if TRACE
  printf("\n---> DPLL:   Implied literal %"PRIu32", by clause %"PRIu32", decision level = %"PRIu32"\n", l, cidx, solver->decision_level);
  fflush(stdout);
#endif
}


/*
 * Literal l implied by a binary clause (of the form { l, l0 }})
 * - l0 = other literal in the clause
 */
static void binary_clause_propagation(sat_solver_t *solver, literal_t l, literal_t l0) {
  assert(l0 < solver->nliterals);

  implied_literal(solver, l, ATAG_BINARY, l0);

#if TRACE
  printf("\n---> DPLL:   Implied literal %"PRIu32", by literal %"PRIu32", decision level = %"PRIu32"\n", l, l0, solver->decision_level);
  fflush(stdout);
#endif
}



/***********************
 *  OCCURRENCE COUNTS  *
 **********************/

/*
 * Scan clause stored in lit[0 ... n-1] and increase occurrence counts
 * for these literals.
 */
static void increase_occurrence_counts(sat_solver_t *solver, uint32_t n, const literal_t *lit) {
  uint32_t i;

  for (i=0; i<n; i++) {
    solver->occ[lit[i]] ++;
  }
}



/**********************
 *  CLAUSE ADDITION   *
 *********************/

/*
 * Add the empty clause
 */
static void add_empty_clause(sat_solver_t *solver) {
  solver->has_empty_clause = true;
}


/*
 * Add unit clause { l }: push l on the assignment stack
 */
static void add_unit_clause(sat_solver_t *solver, literal_t l) {
  assert(lit_is_unassigned(solver, l));
  assign_literal(solver, l);
  solver->units ++;
}


/*
 * Add clause { l0, l1 }
 */
static void add_binary_clause(sat_solver_t *solver, literal_t l0, literal_t l1) {
  solver->binaries ++;
  add_literal_watch(solver, l0, l1);
  add_literal_watch(solver, l1, l0);  
}


/*
 * Add an n-literal clause
 * - n must be at least 2
 * - if solver->preprocess is true, add the new clause to all occurrence lists
 * - otherwise, pick lit[0] and lit[1] as watch literals
 */
static void add_large_clause(sat_solver_t *solver, uint32_t n, const literal_t *lit) {
  cidx_t cidx;

  assert(n >= 2);

#ifndef NDEBUG
  // check that all literals are valid
  for (uint32_t i=0; i<n; i++) {
    assert(lit[i] < solver->nliterals);
  }
#endif

  cidx = clause_pool_add_problem_clause(&solver->pool, n, lit);
  if (solver->preprocess) {
    add_clause_all_watch(solver, n, lit, cidx);
  } else {
    add_clause_watch(solver, lit[0], cidx, lit[1]);
    add_clause_watch(solver, lit[1], cidx, lit[0]);
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
    add_empty_clause(solver);
    return;
  }

  /*
   * Remove duplicates and check for opposite literals l, not(l)
   * (sorting ensure that not(l) is just after l)
   */
  uint_array_sort(lit, n);
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


  /*
   * Add the clause lit[0 ... n-1]
   */
  if (n == 0) {
    add_empty_clause(solver);
  } else if (n == 1) {
    add_unit_clause(solver, lit[0]);
  } else if (n == 2 && !solver->preprocess) {
    add_binary_clause(solver, lit[0], lit[1]);
  } else {
    add_large_clause(solver, n, lit);
  }

  if (solver->preprocess) {
    increase_occurrence_counts(solver, n, lit);
  }
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
  add_clause_watch(solver, lit[0], cidx, lit[1]);
  add_clause_watch(solver, lit[1], cidx, lit[0]);

  return cidx;
}



/****************
 *  CLAUSE LBD  *
 ***************/

/*
 * The Literal-Block Distance is a heuristic estimate of the usefulness
 * of a learned clause. Clauses with low LBD are better.
 * The LBD is the number of distinct decision levels among the literals
 * in a clause.
 *
 * Since backtracking does not clear solver->level[x], we compute the
 * LBD of a learned clause even if some of its literals are not
 * currenlty assigned.  If a literal l in the clause is not currently
 * assigned, then solver->level[var_of(l)] is the decision level of l,
 * at the last time l was assigned.
 */

/*
 * Decision level of literal l
 */
static inline uint32_t d_level(const sat_solver_t *solver, literal_t l) {
  return solver->level[var_of(l)];
}

/*
 * The following function computes the LBD of a clause:
 * - n = number of literals
 * - lit = array of n literals
 */
static uint32_t clause_lbd(sat_solver_t *solver, uint32_t n, const literal_t *lit) {
  tag_map_t *map;
  uint32_t i, r;

  map = &solver->map;
  for (i=0; i<n; i++) {
    tag_map_write(map, d_level(solver, lit[i]), 1);
  }
  r = tag_map_size(map);
  clear_tag_map(map);

  return r;
}


/*
 * Check whether the LBD of a clause is no more than k
 */
static bool clause_lbd_le(sat_solver_t *solver, uint32_t n, const literal_t *lit, uint32_t k) {
  tag_map_t *map;
  uint32_t i;
  bool result;

  result = true;
  map = &solver->map;
  for (i=0; i<n; i++) {
    tag_map_write(map, d_level(solver, lit[i]), 1);
    if (tag_map_size(map) > k) {
      result = false;
      break;
    }
  }
  clear_tag_map(map);

  return result;
}


/************************
 *  GARBAGE COLLECTION  *
 ***********************/

/*
 * Garbage collection compacts the clause pool by removing padding
 * blocks. There are two variants: either compact the whole pool or
 * just the learned clauses. We use a base_idx as starting point for
 * deletion. The base_idx is either 0 (all the clauses) or
 * pool->learned (only the learned clauses).
 */

/*
 * Remove all clause indices >= base_idx from w
 */
static void watch_vector_remove_clauses(watch_t *w, cidx_t base_idx) {
  uint32_t i, j, k, n;

  assert(w != NULL);
  n = w->size;
  j = 0;
  i = 0;
  while (i<n) {
    k = w->data[i];
    if (idx_is_literal(k)) {
      w->data[j] = k;
      j ++;
      i ++;
    } else {
      if (k < base_idx) {
	w->data[j] = k;
	w->data[j+1] = w->data[i+1];
	j += 2;
      }
      i += 2;
    }
  }
  w->size = j;
}

/*
 * Prepare for clause deletion and compaction:
 * - go through all the watch vectors are remove all clause indices >= base_idx
 */
static void prepare_watch_vectors(sat_solver_t *solver, cidx_t base_idx) {
  uint32_t i, n;
  watch_t *w;

  n = solver->nliterals;
  for (i=0; i<n; i++) {
    w = solver->watch[i];
    if (w != NULL) {
      watch_vector_remove_clauses(w, base_idx);
    }
  }
}

/*
 * Mark clause cidx: this means that the clause cidx is the
 * antecedent of a literal l. We mark the clause by setting the
 * high-order bit in the clause's length to 1.
 *
 * This is safe since a clause can't have more than MAX_VARIABLES literals
 * and MAX_VARIABLES < 2^31.
 */
#define CLAUSE_MARK (((uint32_t) 1) << 31)

static inline void mark_clause(clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  pool->data[idx] |= CLAUSE_MARK;
}

/*
 * Mark all the antecedent clauses of idx >= base_idx
 */
static void mark_antecedent_clauses(sat_solver_t *solver, cidx_t base_idx) {
  uint32_t i, n;
  bvar_t x;
  cidx_t cidx;

  n = solver->stack.top;
  for (i=0; i<n; i++) {
    x = var_of(solver->stack.lit[i]);
    assert(var_is_assigned(solver, x));
    if (solver->ante_tag[x] == ATAG_CLAUSE) {
      cidx = solver->ante_data[x];
      if (cidx >= base_idx) {
	mark_clause(&solver->pool, cidx);
      }
    }
  }
}

/*
 * Restore antecedent when clause cidx is moved to new_idx
 * - this is called before the move.
 */
static void restore_clause_antecedent(sat_solver_t *solver, cidx_t cidx, cidx_t new_idx) {
  bvar_t x;

  x = var_of(first_literal_of_clause(&solver->pool, cidx));
  assert(var_is_assigned(solver, x) && solver->ante_tag[x] == ATAG_CLAUSE && 
	 solver->ante_data[x] == cidx);
  solver->ante_data[x] = new_idx;
}

/*
 * Move clause from src_idx to dst_idx
 * - requires dst_idx < src_idx
 * - n = length of the source clause
 */
static void clause_pool_move_clause(clause_pool_t *pool, cidx_t dst_idx, cidx_t src_idx, uint32_t n) {
  uint32_t i;

  assert(dst_idx < src_idx);
  for (i=0; i<n+2; i++) {
    pool->data[dst_idx + i] = pool->data[src_idx + i];
  }
}

/*
 * Compact the pool:
 * - remove all padding blocks
 * - cidx = where to start = base_idx
 *
 * For every clause that's marked and moved, restore the antecedent data.
 */
static void compact_clause_pool(sat_solver_t *solver, cidx_t cidx) {
  clause_pool_t *pool;
  uint32_t k, n, end;
  cidx_t i;

  pool = &solver->pool;

  assert(clause_pool_invariant(pool));

  i = cidx;
  end = pool->learned;
  for (k=0; k<2; k++) {
    /*
     * First iteration: deal with problem clauses (or do nothing)
     * Second iteration: deal with learned clauses.
     */
    while (cidx < end) {
      n = pool->data[cidx];
      if (n == 0) {
	// padding block: skip it
	cidx += padding_length(pool, cidx);
      } else {
	// keep the clause: store it at index i
	assert(i <= cidx);
	if ((n & CLAUSE_MARK) != 0) {
	  // marked clause: restore the antecedent data
	  // and remove the mark
	  n &= ~CLAUSE_MARK;
	  pool->data[cidx] = n;
	  restore_clause_antecedent(solver, cidx, i);
	}
	if (i < cidx) {
	  clause_pool_move_clause(pool, i, cidx, n);
	}
	i += full_length(n);
	cidx += full_length(n);;
      }      
    }
    if (k == 0) {
      assert(end == pool->learned);
      if (i < pool->learned) {
	pool->learned = i;
      }
      end = pool->size; // prepare for next iteration
    }
  }

  assert(end == pool->size);
  pool->size = i;
  pool->available = pool->capacity - i;

  assert(clause_pool_invariant(pool));

}

/*
 * Restore the watch vectors:
 * - scan the clauses starting from index cidx 
 *   and add them to the watch vectors
 */
static void restore_watch_vectors(sat_solver_t *solver, cidx_t cidx) {
  literal_t l0, l1;
  cidx_t end;

  end = solver->pool.size;
  while (cidx < end) {
    l0 = first_literal_of_clause(&solver->pool, cidx);
    l1 = second_literal_of_clause(&solver->pool, cidx);
    add_clause_watch(solver, l0, cidx, l1);
    add_clause_watch(solver, l1, cidx, l0);
    cidx = clause_pool_next_clause(&solver->pool, cidx);
  }
}

/*
 * Garbage collection
 */
static void collect_garbage(sat_solver_t *solver, cidx_t base_index) {
  check_clause_pool_counters(&solver->pool);      // DEBUG
  mark_antecedent_clauses(solver, base_index);
  prepare_watch_vectors(solver, base_index);
  compact_clause_pool(solver, base_index);
  check_clause_pool_learned_index(&solver->pool); // DEBUG
  check_clause_pool_counters(&solver->pool);      // DEBUG
  restore_watch_vectors(solver, base_index);
}


/*********************************
 *  DELETION OF LEARNED CLAUSES  *
 ********************************/

/*
 * Allocate the internal cidx_array for n clauses
 * - n must be positive
 */
static void alloc_cidx_array(sat_solver_t *solver, uint32_t n) {
  assert(solver->cidx_array == NULL && n > 0);
  solver->cidx_array = (cidx_t *) safe_malloc(n * sizeof(cidx_t));
}

/*
 * Delete the array
 */
static void free_cidx_array(sat_solver_t *solver) {
  assert(solver->cidx_array != NULL);
  safe_free(solver->cidx_array);
  solver->cidx_array = NULL;
}

/*
 * Check whether clause cidx is used as an antecedent.
 * (This means that it can't be deleted).
 */
static bool clause_is_locked(const sat_solver_t *solver, cidx_t cidx) {
  bvar_t x0;

  x0 = var_of(first_literal_of_clause(&solver->pool, cidx));
  return solver->ante_tag[x0] == ATAG_CLAUSE && 
    solver->ante_data[x0] == cidx && var_is_assigned(solver, x0);
}


/*
 * Check whether clause cidx should be kept
 * - heuristic: the clause is considered precious if its LDB is 4 or less
 * - this can be changed by setting keep_lbd to something other than 4.
 */
static bool clause_is_precious(sat_solver_t *solver, cidx_t cidx) {
  uint32_t n, k;

  k = solver->keep_lbd;
  n = clause_length(&solver->pool, cidx);
  return n <= k || clause_lbd_le(solver, n, clause_literals(&solver->pool, cidx), k);
}

/*
 * Collect learned clauses indices into solver->cidx_array
 * - initialize the array with size = number of learned clauses
 * - store all clauses that are not locked and not precious into the array
 * - return the number of clauses collected
 */
static uint32_t collect_learned_clauses(sat_solver_t *solver) {
  cidx_t *a;
  cidx_t cidx, end;
  uint32_t i;  

  alloc_cidx_array(solver, solver->pool.num_learned_clauses);

  a = solver->cidx_array;
  i = 0;

  end = solver->pool.size;
  cidx = clause_pool_first_learned_clause(&solver->pool);
  while (cidx < end) {
    if (! clause_is_locked(solver, cidx) &&
	! clause_is_precious(solver, cidx)) {
      assert(i < solver->pool.num_learned_clauses);
      a[i] = cidx;
      i ++;
    }
    cidx = clause_pool_next_clause(&solver->pool, cidx);
  }

  return i;
}

/*
 * Sort cidx_array in increasing activity order
 * - use stable sort
 * - n = number of clauses stored in the cidx_array
 */
// ordering: aux = solver, c1 and c2 are the indices of two learned clauses
static bool less_active(void *aux, cidx_t c1, cidx_t c2) {
  sat_solver_t *solver;
  float act1, act2;

  solver = aux;
  act1 = get_learned_clause_activity(&solver->pool, c1);
  act2 = get_learned_clause_activity(&solver->pool, c2);
  return act1 < act2 || (act1 == act2 && c1 < c2);
}

static void sort_learned_clauses(sat_solver_t *solver, uint32_t n) {
  uint_array_sort2(solver->cidx_array, n, solver, less_active);
}


/*
 * Delete half the learned clauses (Minisat-style)
 */
static void nsat_reduce_learned_clause_set(sat_solver_t *solver) {
  uint32_t i, n, n0;
  cidx_t *a;

  n = collect_learned_clauses(solver);
  sort_learned_clauses(solver, n);
  a = solver->cidx_array;

  check_candidate_clauses_to_delete(solver, a, n); // DEBUG

  // the first half of a contains clauses of low score
  n0 = n/2;
  for (i=0; i<n0; i++) {
    clause_pool_delete_clause(&solver->pool, a[i]);
    solver->stats.learned_clauses_deleted ++;
  }

  free_cidx_array(solver);

  collect_garbage(solver, solver->pool.learned);
  solver->stats.reduce_calls ++;

  check_watch_vectors(solver);
}



/********************************************
 *  SIMPLIFICATION OF THE CLAUSE DATABASE   *
 *******************************************/

/*
 * Cleanup watch vector w:
 * - remove all the assigned (true) literals from w
 */
static void cleanup_watch_vector(sat_solver_t *solver, watch_t *w) {
  uint32_t i, j, k, n;

  assert(solver->decision_level == 0 &&
	 solver->stack.top == solver->stack.prop_ptr &&
	 w != NULL);

  n = w->size;
  j = 0;
  i = 0;
  while (i < n) {
    k = w->data[i];
    if (idx_is_clause(k)) {
      w->data[j] = k;
      w->data[j+1] = w->data[i+1];
      j += 2;
      i += 2;
    } else {
      if (lit_is_unassigned(solver, idx2lit(k))) {
	w->data[j] = k;
	j ++;
      }
      i ++;
    }
  }
  w->size = j;
}


/*
 * Simplify the binary clauses:
 * - if l is assigned at level 0, delete its watched vector
 *   (this assumes that all Boolean propagations have been done).
 * - otherwise, remove the assigned literals from watch[l].
 */
static void simplify_binary_clauses(sat_solver_t *solver) {
  uint32_t i, n;
  watch_t *w;

  assert(solver->decision_level == 0 &&
	 solver->stack.top == solver->stack.prop_ptr);

  n = solver->nliterals;
  for (i=2; i<n; i++) {
    w = solver->watch[i];
    if (w != NULL) {
      switch (lit_value(solver, i)) {
      case BVAL_UNDEF_TRUE:
      case BVAL_UNDEF_FALSE:
	cleanup_watch_vector(solver, w);
	break;

      case BVAL_TRUE:
      case BVAL_FALSE:
	safe_free(w);
	solver->watch[i] = NULL;
	break;
      }
    }
  }
}


/*
 * After deletion: count the number of binary clauses left
 */
static uint32_t num_literals_in_watch_vector(watch_t *w) {
  uint32_t i, n, count;

  assert(w != NULL);
  count = 0;
  n = w->size;
  i = 0;
  while (i < n) {
    if (idx_is_literal(w->data[i])) {
      count ++;
      i ++;
    } else {
      i += 2;
    }
  }
  return count;
}


static uint32_t count_binary_clauses(sat_solver_t *solver) {
  uint32_t i, n, sum;
  watch_t *w;

  sum = 0;
  n = solver->nliterals;
  for (i=2; i<n; i++) {
    w = solver->watch[i];
    if (w != NULL) {
      sum += num_literals_in_watch_vector(w);
    }
  }
  assert((sum & 1) == 0 && sum/2 <= solver->binaries);

  return sum >> 1;
}


/*
 * Simplify the clause that starts at cidx:
 * - remove all literals that are false at the base level
 * - return true if the clause is true
 * - return false otherwise
 */
static bool simplify_clause(sat_solver_t *solver, cidx_t cidx) {
  uint32_t i, j, n;
  literal_t *a;
  literal_t l;

  assert(solver->decision_level == 0 && good_clause_idx(&solver->pool, cidx));
  
  n = clause_length(&solver->pool, cidx);
  a = clause_literals(&solver->pool, cidx);

  j = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    switch (lit_value(solver, l)) {
    case BVAL_FALSE:
      break;

    case BVAL_UNDEF_FALSE:
    case BVAL_UNDEF_TRUE:
      a[j] = l;
      j ++;
      break;

    case BVAL_TRUE:
      return true;
    }
  }

  assert(j >= 2);
  if (j < n) {
    clause_pool_shrink_clause(&solver->pool, cidx, j);
  }

  return false;
}


/*
 * Remove dead antecedents (of literals assigned at level 0)
 * - if l is implied at level 0 by a clause cidx,
 *   then cidx will be deleted by nsat_simplify_clause_databae.
 *   so l ends up with a dead antecedent.
 * - to fix this, we change the ante_tag of all literals
 *   implied by a clause to ATAG_UNIT
 */
static void remove_dead_antecedents(sat_solver_t *solver) {
  uint32_t i, n;
  literal_t l;

  assert(solver->decision_level == 0);

  n = solver->stack.top;
  for (i=0; i<n; i++) {
    l = solver->stack.lit[i];
    assert(solver->level[var_of(l)] == 0);
    solver->ante_tag[var_of(l)] = ATAG_UNIT;
  }
}


/*
 * Simplify all the clauses
 * - remove all false literals
 * - remove all true clauses
 */
static void nsat_simplify_clause_database(sat_solver_t *solver) {
  cidx_t cidx;
  uint32_t d;

  assert(solver->decision_level == 0 && solver->stack.top == solver->stack.prop_ptr);

  simplify_binary_clauses(solver);

  d = 0; // count true clauses
  cidx = clause_pool_first_clause(&solver->pool);
  // Note: pool.size may change within the loop if clauses are deleted
  while (cidx < solver->pool.size) {
    if (simplify_clause(solver, cidx)) {
      d ++;
      clause_pool_delete_clause(&solver->pool, cidx);
    }
    cidx = clause_pool_next_clause(&solver->pool, cidx);
  }

  if (d > 0) {
    solver->stats.prob_clauses_deleted += d;
    remove_dead_antecedents(solver);
    collect_garbage(solver, 0);
  }

  solver->binaries = count_binary_clauses(solver);
  solver->stats.simplify_calls ++;

  check_watch_vectors(solver);
}



/*******************
 *  PREPROCESSING  *
 ******************/

 /*
 * Experiment: print stuff
 */
static void show_occurrence_counts(sat_solver_t *solver) {
  uint32_t i, n, pp, nn;
  uint32_t unused, pure, pospure, elims, maybes;

  unused = 0;
  pure = 0;
  pospure = 0;
  elims = 0;
  maybes = 0;
  n = solver->nvars;
  for (i=1; i<n; i++) {
    pp = solver->occ[pos(i)];
    nn = solver->occ[neg(i)]; 
    if (pp == 0 && nn == 0) {
      unused ++;
    } else if (pp == 0 || nn == 0) {
      if (pp > 0) pospure ++;
      pure ++;
    } else if (pp == 1 || nn == 1 || (pp == 2 && nn == 2)) {
      elims ++;
    } else if (pp <= 10 || nn <= 10) {
      maybes ++;
    }
  }

  fprintf(stderr, "Before preprocessing\n");
  fprintf(stderr, "unused vars          : %"PRIu32"\n", unused);
  fprintf(stderr, "pure literals        : %"PRIu32" (%"PRIu32" positive)\n", pure, pospure);
  fprintf(stderr, "cheap elims          : %"PRIu32"\n", elims);
  fprintf(stderr, "maybe elims          : %"PRIu32"\n", maybes);
  fprintf(stderr, "others               : %"PRIu32"\n\n", solver->nvars - (unused + pure + elims + maybes));
}


/*
 * Statistics after preprocessing
 */
static void show_preprocessing_stats(sat_solver_t *solver) {
  fprintf(stderr, "After preprocessing\n");
  fprintf(stderr, "unit literals        : %"PRIu32"\n", solver->stats.pp_unit_lits);
  fprintf(stderr, "pure literals        : %"PRIu32"\n", solver->stats.pp_pure_lits);
  fprintf(stderr, "deleted clauses      : %"PRIu32"\n", solver->stats.pp_clauses_deleted);
  fprintf(stderr, "nb. of vars          : %"PRIu32"\n", solver->nvars);
  fprintf(stderr, "nb. of unit clauses  : %"PRIu32"\n", solver->units);           // should be zero
  fprintf(stderr, "nb. of bin clauses   : %"PRIu32"\n", solver->binaries);
  fprintf(stderr, "nb. of big clauses   : %"PRIu32"\n\n", solver->pool.num_prob_clauses);

  if (solver->has_empty_clause) {
    fprintf(stderr, "found unsat by preprocessing\n\n");
  }
}


/*
 * QUEUE OF PURE AND UNIT LITERALS
 */
static inline bool clause_is_live(const clause_pool_t *pool, cidx_t cidx) {
  return cidx < pool->size && is_clause_start(pool, cidx);
}

/*
 * Push pure or unit literal l into the queue
 * - l must not be assigned
 * - the function assigns l to true
 * - tag = either ATAG_UNIT or ATAG_PURE
 */
static void pp_push_literal(sat_solver_t *solver, literal_t l, antecedent_tag_t tag) {
  bvar_t v;

  assert(l < solver->nliterals);
  assert(lit_is_unassigned(solver, l));
  assert(solver->decision_level == 0);
  assert(tag == ATAG_UNIT || tag == ATAG_PURE);

  lqueue_push(&solver->queue, l);

  solver->value[l] = BVAL_TRUE;
  solver->value[not(l)] = BVAL_FALSE;

  v = var_of(not(l));
  solver->ante_tag[v] = tag;
  solver->ante_data[v] = 0;
  solver->level[v] = 0;
}

static inline void pp_push_pure_literal(sat_solver_t *solver, literal_t l) {
  pp_push_literal(solver, l, ATAG_PURE);
  solver->stats.pp_pure_lits ++;
}

static inline void pp_push_unit_literal(sat_solver_t *solver, literal_t l) {
  pp_push_literal(solver, l, ATAG_UNIT);
  solver->stats.pp_unit_lits ++;
}


/*
 * Decrement the occurrence counter of l.
 * - if occ[l] goes to zero, add not(l) to the queue as a pure literal (unless
 *   l is already assigned).
 */
static void pp_decrement_occ(sat_solver_t *solver, literal_t l) {
  assert(solver->occ[l] > 0);
  solver->occ[l] --;
  if (solver->occ[l] == 0 && solver->occ[not(l)] > 0 && lit_is_unassigned(solver, l)) {    
    pp_push_pure_literal(solver, not(l));
  }
}

/*
 * Decrement occ counts for all literals in a[0 ... n-1]
 */
static void pp_decrement_occ_counts(sat_solver_t *solver, literal_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    pp_decrement_occ(solver, a[i]);
  }
}

/*
 * Delete clause cidx and update occ counts
 * - if cidx points to a dead clause, do nothing
 */
static void pp_remove_clause(sat_solver_t *solver, cidx_t cidx) {
  literal_t *a;
  uint32_t n;
 
  if (clause_is_live(&solver->pool, cidx)) {
    n = clause_length(&solver->pool, cidx);
    a = clause_literals(&solver->pool, cidx);
    pp_decrement_occ_counts(solver, a, n);
    clause_pool_delete_clause(&solver->pool, cidx);
    solver->stats.pp_clauses_deleted ++;
  }
}

/*
 * Delete all the clauses that contain l (because l is true)
 */
static void pp_remove_true_clauses(sat_solver_t *solver, literal_t l) {
  watch_t *w;
  uint32_t i, n, k;

  assert(lit_is_true(solver, l));

  w = solver->watch[l];
  if (w != NULL) {
    n = w->size;
    for (i=0; i<n; i++) {
      k = w->data[i];
      assert(idx_is_clause(k));
      pp_remove_clause(solver, k);
    }
    // delete w
    safe_free(w);
    solver->watch[l] = NULL;
  }
}

/*
 * Visit clause at cidx and remove all assigned literals
 * - if the clause is dead, do nothing
 * - if it's true remove it
 * - otherwise remove all false literals from the clause
 * - if the result is empty, record this (solver->has_empty_clause := true)
 * - if the result is a unit clause, push the corresponding literals into the queue
 */
static void pp_visit_clause(sat_solver_t *solver, cidx_t cidx) {
  uint32_t i, j, n;
  literal_t *a;
  literal_t l;
  bool true_clause;
 
  if (clause_is_live(&solver->pool, cidx)) {
    n = clause_length(&solver->pool, cidx);
    a = clause_literals(&solver->pool, cidx);
    true_clause = false;

    j = 0;
    for (i=0; i<n; i++) {
      l = a[i];
      switch (lit_value(solver, l)) {
      case BVAL_TRUE:
	true_clause = true; // fall-through intended to keep the occ counts accurate
      case BVAL_FALSE:
	assert(solver->occ[l] > 0);
	solver->occ[l] --;
	break;

      default:
	a[j] = l;
	j ++;
	break;
      }
    }

    if (true_clause) {
      pp_decrement_occ_counts(solver, a, j);
      clause_pool_delete_clause(&solver->pool, cidx);
      solver->stats.pp_clauses_deleted ++;
    } else if (j == 0) {
      add_empty_clause(solver);
      clause_pool_delete_clause(&solver->pool, cidx);
    } else if (j == 1) {
      pp_push_unit_literal(solver, a[0]);
      clause_pool_delete_clause(&solver->pool, cidx);
    } else {
      clause_pool_shrink_clause(&solver->pool, cidx, j);
    }
  }
}


/*
 * Visit all the clauses that contain l (because l is false)
 */
static void pp_visit_clauses_of_lit(sat_solver_t *solver, literal_t l) {
  watch_t *w;
  uint32_t i, n, k;

  assert(lit_is_false(solver, l));

  w = solver->watch[l];
  if (w != NULL) {
    n = w->size;
    for (i=0; i<n; i++) {
      k = w->data[i];
      assert(idx_is_clause(k));
      pp_visit_clause(solver, k);
      if (solver->has_empty_clause) break;
    }
    // delete w
    safe_free(w);
    solver->watch[l] = NULL;
  }
}


/*
 * Initialize the queue: store all unit and pure literals.
 */
static void collect_unit_and_pure_literals(sat_solver_t *solver) {
  uint32_t i, n;
  uint32_t pos_occ, neg_occ;
  
  assert(lqueue_is_empty(&solver->queue));

  n = solver->nvars;
  for (i=1; i<n; i++) {
    switch (var_value(solver, i)) {
    case BVAL_TRUE:
      assert(solver->ante_tag[i] == ATAG_UNIT);
      lqueue_push(&solver->queue, pos(i));
      solver->stats.pp_unit_lits ++;      
      break;

    case BVAL_FALSE:
      assert(solver->ante_tag[i] == ATAG_UNIT);
      lqueue_push(&solver->queue, neg(i));
      solver->stats.pp_unit_lits ++;      
      break;

    default:
      pos_occ = solver->occ[pos(i)];
      neg_occ = solver->occ[neg(i)];
      /*
       * if i doesn't occur at all then both pos_occ/neg_occ are zero.
       * we still record neg(i) as a pure literal in this case to force
       * i to be assigned.
       */
      if (pos_occ == 0) {
	pp_push_pure_literal(solver, neg(i));
      } else if (neg_occ == 0) {
	pp_push_pure_literal(solver, pos(i));
      }
      break;
    }
  }
}


/*
 * Process the queue
 */
static void pp_empty_queue(sat_solver_t *solver) {
  literal_t l;

  while (! lqueue_is_empty(&solver->queue)) {
    l = lqueue_pop(&solver->queue);
    assert(lit_is_true(solver, l));
    assert(solver->ante_tag[var_of(l)] == ATAG_UNIT || 
	   solver->ante_tag[var_of(l)] == ATAG_PURE);
    pp_remove_true_clauses(solver, l);
    if (solver->ante_tag[var_of(l)] == ATAG_UNIT) {
      pp_visit_clauses_of_lit(solver, not(l));
      if (solver->has_empty_clause) {
	reset_lqueue(&solver->queue);
	break;
      }
    }
  }
}


/*
 * END OF PREPROCESSING
 */

/*
 * Cleanup all the watch vectors
 */
static void pp_reset_watch_vectors(sat_solver_t *solver) {
  uint32_t i, n;
  watch_t *w;

  n = solver->nliterals;
  for (i=2; i<n; i++) {
    w = solver->watch[i];
    if (w != NULL) {
      w->size = 0;
    }
  }
}

#ifndef NDEBUG
/*
 * Check that clause at index cidx has no assigned literals.
 */
static bool clause_is_clean(sat_solver_t *solver, cidx_t cidx) {
  uint32_t i, n;
  literal_t *a;

  n = clause_length(&solver->pool, cidx);
  a = clause_literals(&solver->pool, cidx);
  for (i=0; i<n; i++) {
    if (lit_is_assigned(solver, a[i])) {
      return false;
    }
  }
  return true;
}
#endif

/*
 * Scan all live clauses in the pool
 * - remove binary clauses from the pool and move them to the watch vectors
 * - also compact the pool
 */
static void pp_rebuild_watch_vectors(sat_solver_t *solver) {
  clause_pool_t *pool;
  uint32_t n;
  cidx_t i, j;
  literal_t l1, l2;

  pool = &solver->pool;

  assert(clause_pool_invariant(pool));
  assert(pool->learned == pool->size && 
	 pool->num_learned_clauses == 0 && 
	 pool->num_learned_literals == 0);

  pool->num_prob_clauses = 0;
  pool->num_prob_literals = 0;

  i = 0;
  j = 0;
  while (i < pool->size) {
    n = pool->data[i];
    if (n == 0) {
      // padding block: skip it
      i += padding_length(pool, i);
    } else {
      assert(n >= 2);
      assert(clause_is_clean(solver, i));
      l1 = first_literal_of_clause(pool, i);
      l2 = second_literal_of_clause(pool, i);
      if (n == 2) {
	// binary clause
	add_binary_clause(solver, l1, l2);
	i += full_length(2);
      } else {
	// regular clause at index j
	if (j < i) {
	  clause_pool_move_clause(pool, j, i, n);
	}
	pool->num_prob_clauses ++;
	pool->num_prob_literals += n;
	add_clause_watch(solver, l1, j, l2);
	add_clause_watch(solver, l2, j, l1);
	i += full_length(n);
	j += full_length(n);
      }
    }
  }
  pool->learned = j;
  pool->size = j;
  pool->available = pool->capacity - j;

  assert(clause_pool_invariant(pool));
}

/*
 * Shrink watch vectors that are less than 25% full
 */
static void shrink_watch_vectors(sat_solver_t *solver) {
  uint32_t i, n;
  watch_t *w;

  n = solver->nliterals;
  for (i=2; i<n; i++) {
    w = solver->watch[i];
    if (false && w != NULL && w->capacity >= 100 && w->size < (w->capacity >> 2)) {
      solver->watch[i] = shrink_watch(w);
    }
  }
}


static void prepare_for_search(sat_solver_t *solver) {
  check_clause_pool_counters(&solver->pool);      // DEBUG
  solver->units = 0;
  solver->binaries = 0;
  reset_stack(&solver->stack);
  pp_reset_watch_vectors(solver);
  pp_rebuild_watch_vectors(solver);
  shrink_watch_vectors(solver);
  check_clause_pool_counters(&solver->pool);      // DEBUG
  check_watch_vectors(solver);                    // DEBUG
}


/*
 * On entry to preprocess:
 * - watch[l] contains all clauses clauses in which l occurs
 * - occ[l] = number of occurrences of l
 * Unit clauses are stored implicitly in the propagation queue.
 * Binary clauses are stored in the pool.
 *
 * On exit:
 * - all units and pure literals are removed
 * - the watch vectors are ready for solving
 */
static void nsat_preprocess(sat_solver_t *solver) {
  if (solver->verbosity >= 1) {
    show_occurrence_counts(solver);
  }
  collect_unit_and_pure_literals(solver);
  pp_empty_queue(solver);
  if (! solver->has_empty_clause) {
    prepare_for_search(solver);
  }
  if (solver->verbosity >= 1) {
    show_preprocessing_stats(solver);
  }
}



/**************************
 *  BOOLEAN PROPAGATION   *
 *************************/

/*
 * Conflict: binary clause {l0, l1} is false
 */
static void record_binary_conflict(sat_solver_t *solver, literal_t l0, literal_t l1) {
  assert(lit_is_false(solver, l0) && lit_is_false(solver, l1));

#if TRACE
  printf("\n---> DPLL:   Binary conflict: %"PRIu32" %"PRIu32"\n", l0, l1);
  fflush(stdout);
#endif

  solver->conflict_tag = CTAG_BINARY;
  solver->conflict_buffer[0] = l0;
  solver->conflict_buffer[1] = l1;
  solver->stats.conflicts ++;
}

/*
 * For debugging: check that clause cidx is false
 */
#ifndef NDEBUG
static bool clause_is_false(const sat_solver_t *solver, cidx_t cidx) {
  literal_t *l;
  uint32_t i, n;

  assert(good_clause_idx(&solver->pool, cidx));
  n = clause_length(&solver->pool, cidx);
  l = clause_literals(&solver->pool, cidx);
  for (i=0; i<n; i++) {
    if (!lit_is_false(solver, l[i])) {
      return false;
    }
  }
  return true;
}
#endif

/*
 * Conflict: clause cidx is false
 */
static void record_clause_conflict(sat_solver_t *solver, cidx_t cidx) {
  assert(clause_is_false(solver, cidx));

#if TRACE
  printf("\n---> DPLL:   Clause conflict: cidx = %"PRIu32"\n");
  fflush(stdout);
#endif

  solver->conflict_tag = CTAG_CLAUSE;
  solver->conflict_index = cidx;
  solver->stats.conflicts ++;
}


/*
 * Propagation from literal l0
 * - l0 must be false in the current assignment
 * - sets solver->conflict_tag if there's a conflict
 */
static void propagate_from_literal(sat_solver_t *solver, literal_t l0) {
  watch_t *w;
  literal_t *lit;
  uint32_t i, j, n, k, len, t;
  literal_t l, l1;
  bval_t vl;

  assert(lit_is_false(solver, l0));

  w = solver->watch[l0];
  if (w == NULL || w->size == 0) return; // nothing to do

  n = w->size;
  j = 0;
  i = 0;
  while (i < n) {
    k = w->data[i];
    w->data[j] = k; // Keep k in w. We'll undo this later if needed.
    i ++;
    j ++;
    if (idx_is_literal(k)) {
      /*
       * Binary clause
       */
      l = idx2lit(k);
      vl = lit_value(solver, l);
      if (vl == BVAL_TRUE) continue;
      if (vl == BVAL_FALSE) {
	record_binary_conflict(solver, l0, l);
	goto conflict;
      }
      assert(is_unassigned_val(vl));
      binary_clause_propagation(solver, l, l0);
      continue;

    } else {
      /*
       * Clause in the pool
       */
      // get the blocker
      l = w->data[i];
      w->data[j] = l;
      i ++;
      j ++;
      if (lit_is_true(solver, l)) {
	continue;
      }

      len = clause_length(&solver->pool, k);
      lit = clause_literals(&solver->pool, k);
      assert(lit[0] == l0 || lit[1] == l0);
      // Get the other watched literal in clause k
      l = lit[0] ^ lit[1] ^ l0;
      // If l is true, nothing to do
      vl = lit_value(solver, l);
      if (vl == BVAL_TRUE) {
	w->data[j-1] = l; // change blocker
	continue;
      }

      // Force l to go into lit[0] and l0 into lit[1]
      lit[0] = l;
      lit[1]  = l0;

      // Search for an unassigned or true literal in lit[2 ... len-1]
      for (t=2; t<len; t++) {
	if (! lit_is_false(solver, lit[t])) {
	  // lit[t] is either true or not assigned.
	  // It can replace l0 as watched literal
	  l1 = lit[t];
	  lit[1] = l1;
	  lit[t] = l0;
	  add_clause_watch(solver, l1, k, l);
	  j -= 2; // remove [k, blocker] from l0's watch vector
	  goto done;
	}
      }

      // All literals in lit[1 ... len-1] are false
      assert(t == len);
      if (vl == BVAL_FALSE) {
	record_clause_conflict(solver, k);
	goto conflict;
      }
      assert(is_unassigned_val(vl));
      clause_propagation(solver, l, k);
    done:
      continue;
    }
  }
  w->size = j;
  return;

 conflict:
  while (i<n) {
    w->data[j] = w->data[i];
    j ++;
    i ++;
  }
  w->size = j;
}


/*
 * Boolean propagation
 * - on entry, solver->conflict_tag must be CTAG_NONE
 * - on exit, it's set to CTAG_BINARY or CTAG_CLAUSE if there's a conflict
 */
static void nsat_boolean_propagation(sat_solver_t *solver) {
  literal_t l;
  uint32_t i;  

  assert(solver->conflict_tag == CTAG_NONE);

  for (i = solver->stack.prop_ptr; i< solver->stack.top; i++) {
    l = not(solver->stack.lit[i]);
    propagate_from_literal(solver, l);
    if (solver->conflict_tag != CTAG_NONE) {
      return;
    }
  }
  solver->stack.prop_ptr = i;

  check_propagation(solver);
}


/******************
 *  BACKTRACKING  *
 *****************/

/*
 * Backtrack to back_level
 * - undo all assignments at levels >= back_level + 1
 * - solver->decision_level must be larger than back_level
 *   (otherwise level_index[back_level + 1] may not be set properly).
 */
static void backtrack(sat_solver_t *solver, uint32_t back_level) {
  uint32_t i, d;
  literal_t l;
  bvar_t x;

  assert(back_level < solver->decision_level);

  d = solver->stack.level_index[back_level + 1];
  i = solver->stack.top;
  while (i > d) {
    i --;
    l = solver->stack.lit[i];
    x = var_of(l);
    assert(lit_is_true(solver, l) && solver->level[x] > back_level);
    solver->value[pos(x)] ^= (uint8_t) 0x2;   // clear assign bit
    solver->value[neg(x)] ^= (uint8_t) 0x2;   // clear assign bit
    assert(var_is_unassigned(solver, x));
    heap_insert(&solver->heap, x);
  }

  solver->stack.top = i;
  solver->stack.prop_ptr = i;
  solver->decision_level = back_level;
}



/*
 * Check whether all variables assigned at level k have activity less than ax
 */
static bool level_has_lower_activity(sat_solver_t *solver, double ax, uint32_t k) {
  sol_stack_t *stack;
  uint32_t i, n;
  bvar_t x;

  assert(k <= solver->decision_level);
  stack = &solver->stack;

  // i := start of level k
  // n := end of level k
  i = stack->level_index[k];
  n = stack->top;
  if (k < solver->decision_level) {
    n = stack->level_index[k+1];
  }

  while (i < n) {
    x = var_of(stack->lit[i]);
    assert(var_is_assigned(solver, x) && solver->level[x] == k);
    if (solver->heap.activity[x] >= ax) {
      return false;
    }
    i ++;
  }

  return true;
}

/*
 * Partial restart:
 * - find the unassigned variable of highest activity
 * - keep all the decision levels that have at least one variable
 *   with activity higher than that.
 */
static void partial_restart(sat_solver_t *solver) {
  double ax;
  bvar_t x;
  uint32_t i, n;

  assert(solver->decision_level > 0);
  cleanup_heap(solver);

  if (heap_is_empty(&solver->heap)) {
    // full restart
    backtrack(solver, 0);
  } else {
    x = solver->heap.heap[1];
    assert(var_is_unassigned(solver, x));
    ax = solver->heap.activity[x];

    n = solver->decision_level;
    for (i=1; i<=n; i++) {
      if (level_has_lower_activity(solver, ax, i)) {
	backtrack(solver, i-1);
	break;
      }
    }
  }
}



/*******************************************************
 *  CONFLICT ANALYSIS AND CREATION OF LEARNED CLAUSES  *
 ******************************************************/

/*
 * During conflict resolution, we build a clause in solver->buffer.
 * Except at the very end, all literals in this buffer have decision
 * level < conflict level. To prevent duplicates, we mark all of them.
 *
 * In addition, we also mark the literals that must be resolved.
 * These literals have decision level equal to the conflict level.
 */

/*
 * Set/clear/test the mark on variable x
 * - we use the high order bit of the ante_tag
 * - if this bit is 1, x is marked
 */
static inline void mark_variable(sat_solver_t *solver, bvar_t x) {
  assert(x < solver->nvars);
  solver->ante_tag[x] |= (uint8_t) 0x80;
}

static inline void unmark_variable(sat_solver_t *solver, bvar_t x) {
  assert(x < solver->nvars);
  solver->ante_tag[x] &= (uint8_t) 0x7F;
}

static inline bool variable_is_marked(const sat_solver_t *solver, bvar_t x) {
  assert(x < solver->nvars);
  return (solver->ante_tag[x] & (uint8_t) 0x80) != 0;
}

/*
 * Short cuts: use literal
 */
static inline bool literal_is_marked(const sat_solver_t *solver, literal_t l) {
  return variable_is_marked(solver, var_of(l));
}

/*
 * Process literal l during conflict resolution.
 * - l is either a part of the learned clause or a literal to resolve
 * - if l is marked do nothing (already seen)
 * - if l has decision level 0, ignore it
 * - otherwise:
 *     mark l
 *     increase variable activity
 *     if l's decision_level < conflict level then add l to the buffer
 *     
 * - return 1 if l is to be resolved
 * - return 0 otherwise
 */
static uint32_t process_literal(sat_solver_t *solver, literal_t l) {
  bvar_t x;

  x = var_of(l);

  assert(solver->level[x] <= solver->decision_level);
  assert(lit_is_false(solver, l));

  if (! variable_is_marked(solver, x) && solver->level[x] > 0) {
    mark_variable(solver, x);
    increase_var_activity(&solver->heap, x);
    if (solver->level[x] == solver->decision_level) {
      return 1;
    }
    lbuffer_push(&solver->buffer, l);
  }

  return 0;
}

/*
 * Process clause cidx:
 * - process literals starting from i0
 * - i0 is either 0 or 1
 * - increase the clause activity if it's a learned clause
 * - return the number of literals to resolved
 */
static uint32_t process_clause(sat_solver_t *solver, cidx_t cidx, uint32_t i0) {
  literal_t *lit;
  uint32_t i, n, toresolve;

  assert(i0 <= 1);

  if (is_learned_clause_idx(&solver->pool, cidx)) {
    increase_clause_activity(solver, cidx);
  }

  toresolve = 0;
  n = clause_length(&solver->pool, cidx);
  lit = clause_literals(&solver->pool, cidx);
  for (i=i0; i<n; i++) {
    toresolve += process_literal(solver, lit[i]);
  }
  return toresolve;
}


/*
 * Build learned clause and find UIP
 *
 * Result:
 * - the learned clause is stored in solver->buffer
 * - the implied literal is in solver->buffer.data[0]
 * - all literals in the learned clause are marked
 */
static void analyze_conflict(sat_solver_t *solver) {
  literal_t *stack;
  literal_t b;
  bvar_t x;
  uint32_t j, unresolved;

  assert(solver->decision_level > 0);

  unresolved = 0;
  lbuffer_reset_and_reserve(&solver->buffer); // make room for one literal

  /*
   * Scan the conflict clause
   */
  if (solver->conflict_tag == CTAG_BINARY) {
    unresolved += process_literal(solver, solver->conflict_buffer[0]);
    unresolved += process_literal(solver, solver->conflict_buffer[1]);
  } else {
    assert(solver->conflict_tag == CTAG_CLAUSE);
    unresolved += process_clause(solver, solver->conflict_index, 0);
  }

  /*
   * Scan the assignment stack from top to bottom and process
   * the antecedent of all literals to resolve.
   */
  stack = solver->stack.lit;
  j = solver->stack.top;
  for (;;) {
    j --;    
    b = stack[j];
    assert(d_level(solver, b) == solver->decision_level);
    if (literal_is_marked(solver, b)) {
      if (unresolved == 1) {
	// found UIP
	solver->buffer.data[0] = not(b);
	break;
      } else {
	unresolved --;
	x = var_of(b);
	unmark_variable(solver, x);
	if (solver->ante_tag[x] == ATAG_BINARY) {
	  // solver->ante_data[x] = antecedent literal
	  unresolved += process_literal(solver, solver->ante_data[x]);
	} else {
	  assert(solver->ante_tag[x] == ATAG_CLAUSE);
	  assert(first_literal_of_clause(&solver->pool, solver->ante_data[x]) == b);
	  // solver->ante_data[x] = antecedent clause
	  unresolved += process_clause(solver, solver->ante_data[x], 1);
	}
      }
    }
  }

  check_marks(solver);
}


/*
 * CLAUSE SIMPLIFICATION
 */

/*
 * Check whether literal l is redundant (can be removed from the learned clause)
 * - l must be a literal in the learned clause
 * - it's redundant if it's implied by other literals in the learned clause
 * - we assume that all these literals are marked.
 *
 * To check this, we explore the implication grapsh recursively from l.
 * Variables already visited are marked in solver->map:
 * - solver->map[x] == NOT_SEEN means x has not been seen yet
 * - solver->map[x] == IMPLIED means x is 'implied by marked literals'
 * - solver->map[x] == NOT_IMPLIED means x is 'not implied by marked literals'
 *
 * We use the following rules:
 * - a decision literal is not removable
 * - if l all immediate predecessors of l are marked or are are removable
 *   then l is removable.
 * - if one of l's predecessor is not marked and not removable then l
 *   is not removable.
 */
enum {
  NOT_SEEN = 0,
  IMPLIED = 1,
  NOT_IMPLIED = 2
};

// number of predecessors of x in the implication graph
static uint32_t num_predecessors(sat_solver_t *solver, bvar_t x) {
  uint32_t n;

  if (solver->ante_tag[x] == ATAG_BINARY) {
    n = 1;
  } else {
    assert(solver->ante_tag[x] == ATAG_CLAUSE);
    n = clause_length(&solver->pool, solver->ante_data[x]) - 1;
  }
  return n;
}

// get the i-th predecessor of x
static bvar_t predecessor(sat_solver_t *solver, bvar_t x, uint32_t i) {
  literal_t *lit;
  literal_t l;

  if (solver->ante_tag[x] == ATAG_BINARY) {
    assert(i == 0);
    l = solver->ante_data[x];
  } else {
    assert(i < clause_length(&solver->pool, solver->ante_data[x]) - 1);
    lit = clause_literals(&solver->pool, solver->ante_data[x]);
    l = lit[i + 1];
  }
  return var_of(l);
}

static bool implied_by_marked_literals(sat_solver_t *solver, literal_t l) {
  gstack_t *gstack;
  tag_map_t *map;
  gstack_elem_t *top;
  bvar_t x, y;
  uint32_t i;
  
  x = var_of(l);
  map = &solver->map;

  if (variable_is_marked(solver, x) || solver->ante_tag[x] == ATAG_UNIT || tag_map_read(map, x) == IMPLIED) {
    return true;
  }
  if (solver->ante_tag[x] == ATAG_DECISION || tag_map_read(map, x) == NOT_IMPLIED) {
    return false;
  }

  gstack = &solver->gstack;
  assert(gstack_is_empty(gstack));
  gstack_push_var(gstack, x, 0);

  do {
    top = gstack_top(gstack);
    x = top->var;
    if (top->index == num_predecessors(solver, x)) {
      tag_map_write(map, x, IMPLIED);
      gstack_pop(gstack);
    } else {
      y = predecessor(solver, x, top->index);
      top->index ++;
      if (variable_is_marked(solver, y) || solver->ante_tag[y] == ATAG_UNIT || tag_map_read(map, y) == IMPLIED) {
	continue;
      }
      if (solver->ante_tag[y] == ATAG_DECISION || tag_map_read(map, y) == NOT_IMPLIED) {
	goto not_implied;
      }
      gstack_push_var(gstack, y, 0);
    }
  } while (! gstack_is_empty(gstack));

  return true;

 not_implied:
  for (i=0; i<gstack->top; i++) {
    tag_map_write(map, gstack->data[i].var, NOT_IMPLIED);
  }
  reset_gstack(gstack);
  return false;
}

static bool literal_is_redundant(sat_solver_t *solver, literal_t l) {
  literal_t *lit;
  bvar_t x;
  antecedent_tag_t atag;
  cidx_t cidx;
  uint32_t i, n;

  x = var_of(l);
  assert(var_is_assigned(solver, x) && variable_is_marked(solver, x));

  atag = solver->ante_tag[x] & 0x7F; // remove mark bit
  switch (atag) {
  case ATAG_BINARY:
    // ante_data[x] = literal that implies not(l)
    return implied_by_marked_literals(solver, solver->ante_data[x]);

  case ATAG_CLAUSE:
    // ante_data[x] = clause that implies not(l)
    cidx = solver->ante_data[x];
    n = clause_length(&solver->pool, cidx);
    lit = clause_literals(&solver->pool, cidx);
    assert(lit[0] == not(l));
    for (i=1; i<n; i++) {
      if (! implied_by_marked_literals(solver, lit[i])) {
	return false;
      }
    }
    return true;

  default:
    assert(atag == ATAG_DECISION);
    return false;
  }
}


/*
 * Simplify the learned clause:
 * - it's in solver->buffer
 * - all literals in solver->buffer are marked
 * - solver->buffer.data[0] is the implied literal
 * - all other literals have a decision level < solver->decision_level
 *
 * On exit:
 * - the simplified learned clause is in solver->buffer.
 * - all marks are removed.
 */
static void simplify_learned_clause(sat_solver_t *solver) {
  lbuffer_t *buffer;
  uint32_t i, j, n;
  literal_t l;

  assert(solver->aux.size == 0);

  buffer = &solver->buffer;
  n = buffer->size;
  j = 1;
  for (i=1; i<n; i++) { // The first literal is not redundant
    l = buffer->data[i];
    if (literal_is_redundant(solver, l)) {
      // move l to the aux buffer to clean the marks later
      lbuffer_push(&solver->aux, l);
      solver->stats.subsumed_literals ++;
    } else {
      // keep l into buffer
      buffer->data[j] = l;
      j ++;
    }
  }
  buffer->size = j;

  // cleanup: remove marks and reset the map
  clear_tag_map(&solver->map);
  for (i=0; i<j; i++) {
    unmark_variable(solver, var_of(buffer->data[i]));
  }
  n = solver->aux.size;
  for (i=0; i<n; i++) {
    unmark_variable(solver, var_of(solver->aux.data[i]));
  }
  reset_lbuffer(&solver->aux);

  check_all_unmarked(solver);
}


/*
 * Prepare for bracktracking:
 * - search for a literal of second highest decision level in
 *   the learned clause.
 * - solver->buffer contains the learned clause.
 * - the implied literal is in solver->buffer.data[0]
 */
static void prepare_to_backtrack(sat_solver_t *solver) {
  uint32_t i, j, d, x, n;
  literal_t l, *b;

  b = solver->buffer.data;
  n = solver->buffer.size;

  if (n == 1) {
    solver->backtrack_level = 0;
    return;
  }

  j = 1;
  l = b[1];
  d = d_level(solver, l);
  for (i=2; i<n; i++) {
    x = d_level(solver, b[i]);
    if (x > d) {
      d = x;
      j = i;
    }
  }

  // swap b[1] and b[j]
  b[1] = b[j];
  b[j] = l;

  // record backtrack level
  solver->backtrack_level = d;
}


/*
 * Update the exponential moving averages used by the restart heuristics
 *
 * We have 
 *     ema_0 = 0
 *     ema_t+1 = 2^(32 - k) x + (1 - 2^k) ema_t
 * where k is less than 32 and x is the lbd of the learned clause
 * - as in the paper by Biere & Froehlich, we use
 *    k = 5  for the 'fast' ema
 *    k = 14 for the 'slow' ema
 * 
 * For blocking restarts, we use another exponential moving average:
 *     blocking_ema_{t+1} = 2^(32 - k) t + (1 - 2^k) blocking_ema_t
 * where k=12 and t = number of assigned variables (a.k.a., trail size).
 *
 * Also, the heuristics use two counters that are incremented here.
 *
 * NOTE: these updates can't overflow: the LDB is bounded by U < 2^30
 * then we have ema <= 2^32*U. Same thing for the number of assigned
 * variables.
 */
static void update_emas(sat_solver_t *solver, uint32_t x) {
  solver->slow_ema -= solver->slow_ema >> 14;
  solver->slow_ema += ((uint64_t) x) << 18;  
  solver->fast_ema -= solver->fast_ema >> 5;
  solver->fast_ema += ((uint64_t) x) << 27;
  solver->fast_count ++;
}

static void update_blocking_ema(sat_solver_t *solver) {
  solver->blocking_ema -= solver->blocking_ema >> 12;
  solver->blocking_ema += ((uint64_t) solver->stack.top) << 20;
  solver->blocking_count ++;
}

/*
 * Resolve a conflict and add a learned clause
 * - solver->decision_level must be positive
 */
static void resolve_conflict(sat_solver_t *solver) {
  uint32_t n, d;
  literal_t l;
  cidx_t cidx;
  //  uint32_t clevel;

  //  clevel = solver->decision_level; // before resolving the conflict (used for statistics)
  update_blocking_ema(solver);
  analyze_conflict(solver);
  simplify_learned_clause(solver);
  prepare_to_backtrack(solver);
  backtrack(solver, solver->backtrack_level);

  // clear the conflict flag
  solver->conflict_tag = CTAG_NONE;

  // update statistics
  n = solver->buffer.size;
  d = clause_lbd(solver, n, solver->buffer.data);
  update_emas(solver, d);

  // add the learned clause
  l = solver->buffer.data[0];
  if (n >= 3) {
    cidx = add_learned_clause(solver, n, solver->buffer.data);
    clause_propagation(solver, l, cidx);
  } else if (n == 2) {
    add_binary_clause(solver, l, solver->buffer.data[1]);
    binary_clause_propagation(solver, l, solver->buffer.data[1]);
  } else {
    assert(n > 0);
    add_unit_clause(solver, l);
  }

  //  export_conflict_stat(d, clevel, solver->backtrack_level, solver->slow_ema, solver->fast_ema, solver->blocking_ema);
}





/*****************************
 *  MAIN SOLVING PROCEDURES  *
 ****************************/

/*
 * Select an unassigned decision variable
 * - return 0 if all variables are assigned
 */
static bvar_t nsat_select_decision_variable(sat_solver_t *solver) {
  uint32_t rnd;
  bvar_t x;

  if (solver->randomness > 0) {
    rnd = random_uint32(solver) & VAR_RANDOM_MASK;
    if (rnd < solver->randomness) {
      x = random_uint(solver, solver->nvars);
      if (var_is_unassigned(solver, x)) {
	assert(x > 0);
	solver->stats.random_decisions ++;
	return x;
      }
    }
  }

  /*
   * Unassigned variable of highest activity
   */
  while (! heap_is_empty(&solver->heap)) {
    x = heap_get_top(&solver->heap);
    if (var_is_unassigned(solver, x)) {
      assert(x > 0);
      return x;
    }
  }

  /*
   * Check the variables in [heap->vmax ... heap->size - 1]
   */
  x = solver->heap.vmax;
  while (x < solver->heap.size) {
    if (var_is_unassigned(solver, x)) {
      solver->heap.vmax = x+1;
      return x;
    }
    x ++;
  }

  assert(x == solver->heap.size);
  solver->heap.vmax = x;

  return 0;
}


/*
 * Glucose-style restart condition:
 * 1) solver->blocking_ema is a moving average of the trail size
 *    after each conflict.
 * 2) solver->fast_ema is an estimate of the quality of the recently
 *    learned clauses.
 * 3) solver->slow_ema is an estimate of the average quality of all
 *    learned clauses.
 *
 * Intuition:
 * - if the current trail size is larger than blocking_ema, we may
 *   be close to finding a satisfying assignment so we don't want to
 *   restart.
 * - if solver->fast_ema is larger than solver->slow_ema then recent
 *   learned clauses don't seem too good. We want to restart.
 *
 * To make this more precise: we use two magic constants:
 * - K_0 = 1/1.4 (approximately)
 * - K   = 0.8   (approximately)
 * Larger than average trail_size is 'trail_size * K_0 > blocking_ema'
 * Worse than average learned clauses is 'fast_ema * K > slow_ema'

 * Before we use 'blocking_ema', we want to make sure we have at least
 * 5000 samples in there. We count these samples in solver->blocking_count.
 * To avoid restarting everytime, we also keep track of the number of
 * samples used from which fast_ema is computed (in solver->fast_count).
 * We wait until fast_count >= 50 before restarting.
 *
 * For our fixed point implementation, we use 
 *   K_0 = (1 - 1/2^2 - 1/2^5 - 1/2^8) = 0.71484375
 *   K   = (1 - 1/2^3 - 1/2^4 - 1/2^6) = 0.796875
 *
 * The Glucose original uses moving average/long-term average
 * instead of exponential moving averages. (cf. Biere & Froehlich).
 */
static bool glucose_restart(sat_solver_t *solver) {
  uint64_t aux;

  if (solver->blocking_count >= 5000) {
    aux = ((uint64_t) solver->stack.top) << 32;  // trail size
    aux -= (aux >> 2) + (aux >> 5) + (aux >> 8); // K_0 * trail size 
    if (aux > solver->blocking_ema) {
      solver->fast_count = 0; // delay the next restart
      return false;
    }
  }

  if (solver->fast_count >= 50) {
    aux = solver->fast_ema;
    aux -= (aux >> 3) + (aux >> 4) + (aux >> 6); // K * fast_ema
    if (aux > solver->slow_ema) {
      solver->fast_count = 0;
      return true;
    }
  }

  return false;
}



/*
 * Preferred literal when x is selected as decision variable.
 * - we pick l := pos(x) then check whether value[l] is 0b00 or 0b01
 * - in the first case, the preferred value for l is false so we return not(l)
 */
static inline literal_t preferred_literal(const sat_solver_t *solver, bvar_t x) {
  literal_t l;

  assert(var_is_unassigned(solver, x));

  l = pos(x);
  /*
   * Since l is not assigned, value[l] is either BVAL_UNDEF_FALSE (i.e., 0) 
   * or BVAL_UNDEF_TRUE (i.e., 1).
   *
   * We return l if value[l] = BVAL_UNDEF_TRUE = 1. 
   * We return not(l) if value[l] = BVAL_UNDEF_FALSE = 0.
   * Since not(l) is l^1, the returned value is (l ^ 1 ^ value[l]).
   */
  l ^= 1 ^ solver->value[l];
  assert((var_prefers_true(solver, x) && l == pos(x)) ||
	 (!var_prefers_true(solver, x) && l == neg(x)));

  return l;
}


/*
 * Search until we get sat/unsat or we restart
 * - restart is based on the LBD/Glucose heuristics as modified by
 *   Biere & Froehlich.
 */
static void sat_search(sat_solver_t *solver) {
  bvar_t x;

  assert(solver->stack.prop_ptr == solver->stack.top);

  check_propagation(solver);
  check_watch_vectors(solver);

  for (;;) {
    nsat_boolean_propagation(solver);
    if (solver->conflict_tag == CTAG_NONE) {
      // No conflict

      // Check for restarts
      if (glucose_restart(solver)) {
	break;
      }
      // Garbage collection
      if (solver->pool.num_learned_clauses > solver->reduce_threshold) {
	nsat_reduce_learned_clause_set(solver);
	check_watch_vectors(solver);
	solver->reduce_threshold = (uint32_t) (solver->reduce_threshold * REDUCE_FACTOR);
	//  solver->reduce_threshold += 300; // Glucose
      }

      x = nsat_select_decision_variable(solver);
      if (x == 0) {
	solver->status = STAT_SAT;
	break;
      }
      nsat_decide_literal(solver, preferred_literal(solver, x));
    } else {
      // Conflict
      if (solver->decision_level == 0) {
	solver->status = STAT_UNSAT;
	break;
      }
      resolve_conflict(solver);
      check_watch_vectors(solver);

      decay_clause_activities(solver);
      decay_var_activities(&solver->heap);
    }
  }
}


/*
 * Progress status
 */
static void report_status(sat_solver_t *solver, uint32_t count) {
  double lits_per_clause, slow, fast;

  if ((count & 0x3F) == 0) {
    fprintf(stderr, "\n");
    fprintf(stderr, "-------------------------------------------------------------------------------------------------\n");
    fprintf(stderr, "|     EMAS      | Conf.     Del.    |  Binary   |      Original     |          Learned          |\n");
    fprintf(stderr, "| Slow    Fast  |         Threshold |  Clauses  |   Clauses   Lits. |   Clauses  Lits. Lits/Cl. |\n");
    fprintf(stderr, "-------------------------------------------------------------------------------------------------\n");
  }

  lits_per_clause = 0.0;
  if (solver->pool.num_learned_clauses > 0) {
    lits_per_clause = ((double) solver->pool.num_learned_literals) / solver->pool.num_learned_clauses;
  }
  slow = ((double) solver->slow_ema)/4.3e9;
  fast = ((double) solver->fast_ema)/4.3e9;
  fprintf(stderr, "| %6.2f %6.2f | %7"PRIu64"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu32" | %8"PRIu32" %8"PRIu32" %7.1f |\n",
	  slow, fast,
	  solver->stats.conflicts, solver->reduce_threshold,
	  solver->binaries,
	  solver->pool.num_prob_clauses, solver->pool.num_prob_literals,
	  solver->pool.num_learned_clauses, solver->pool.num_learned_literals, lits_per_clause);
  fflush(stderr);
}


/*
 * Number of literals assigned at level 0
 * - this is used to decide whether to call simplify_clause_database
 */
static uint32_t level0_literals(sat_solver_t *solver) {
  uint32_t n;

  n = solver->stack.top;
  if (solver->decision_level > 0) {
    n = solver->stack.level_index[1];
  }
  return n;
}


/*
 * Solving procedure
 */
solver_status_t nsat_solve(sat_solver_t *solver) {
  uint32_t i;

  //  open_stat_file();

  if (solver->has_empty_clause) {
    solver->status = STAT_UNSAT;
    return STAT_UNSAT;
  }

  solver->simplify_bottom = 0;
  solver->simplify_props = 0;
  solver->simplify_next = 0;    // number of propagations before next call to simplify_clause_database

  if (solver->preprocess) {
    nsat_preprocess(solver);
    if (solver->has_empty_clause) {
      solver->status = STAT_UNSAT;
      return STAT_UNSAT;
    }
  }  else {
    // One round of propagation + removal of true clauses
    nsat_boolean_propagation(solver);
    if (solver->conflict_tag != CTAG_NONE) {
      solver->status = STAT_UNSAT;
      return STAT_UNSAT;
    }
    if (solver->units > 0) {
      nsat_simplify_clause_database(solver);
      solver->simplify_bottom = solver->stack.top;
      solver->simplify_props = solver->stats.propagations;
      solver->simplify_next = solver->pool.num_prob_literals; 
    }
  }


  /*
   * Counter for report status
   */
  i = 0;

  /*
   * Glucose-style EMA for restarts
   */
  solver->slow_ema = 0;
  solver->fast_ema = 0;
  solver->blocking_ema = 0;
  solver->fast_count = 0;
  solver->blocking_count = 0;
  solver->stats.starts = 0;


  /*
   * Reduce strategy: as in minisat
   */
   solver->reduce_threshold = solver->pool.num_prob_clauses/4;
   if (solver->reduce_threshold < MIN_REDUCE_THRESHOLD) {
     solver->reduce_threshold = MIN_REDUCE_THRESHOLD;
   }
  //  solver->reduce_threshold = 2000; // Glucose

  for (;;) {
    if (solver->verbosity >= 2) {
      report_status(solver, i);
      i ++;
    }
    solver->stats.starts ++;
    sat_search(solver);
    if (solver->status != STAT_UNKNOWN) break;
    
    // restart
    if (solver->decision_level > 0) {
      if (level0_literals(solver) > solver->simplify_bottom &&
	  solver->stats.propagations >= solver->simplify_props + solver->simplify_next) {
	// force full restart to call simplify
	backtrack(solver, 0);
      } else {
	partial_restart(solver);
      }
    }

    // call simplify
    if (solver->decision_level == 0 &&
	level0_literals(solver) > solver->simplify_bottom &&
	solver->stats.propagations >= solver->simplify_props + solver->simplify_next) {
      nsat_simplify_clause_database(solver);
      solver->simplify_bottom = solver->stack.top;
      solver->simplify_props = solver->stats.propagations;
      solver->simplify_next = solver->pool.num_prob_literals + solver->pool.num_learned_literals;      
    }
  }

  if (solver->verbosity >= 2) {
    fprintf(stderr, "-------------------------------------------------------------------------------------------------\n\n");
  }

  //  close_stat_file();

  return solver->status;
}


/************
 *  MODELS  *
 ***********/

/*
 * Return the model: copy all variable value into val
 * - val's size must be at least solver->nvars
 * - val[0] is always true
 */
void nsat_get_allvars_assignment(const sat_solver_t *solver, bval_t *val) {
  uint32_t i, n;

  n = solver->nvars;
  for (i=0; i<n; i++) {
    val[i] = var_value(solver, i);
  }
}


/*
 * Copy all true literals in array a:
 * - a must have size >= solver->nvars.
 * return the number of literals added to a.
 */
uint32_t nsat_get_true_literals(const sat_solver_t *solver, literal_t *a) {
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

/*
 * Check the counters, assuming pool->learned and pool->size are correct.
 */
static void check_clause_pool_counters(const clause_pool_t *pool) {
  if (!good_counters(pool)) {
    fprintf(stderr, "**** BUG: inconsistent pool counters ****\n");
    fflush(stderr);
  }
}


/*
 * Check that all problem clauses have index < pool->learned
 * and that all learned clause have index >= pool->learned;
 * This assumes that pool->num_prob_clauses is correct.
 */
static void check_clause_pool_learned_index(const clause_pool_t *pool) {
  cidx_t cidx, end, next;
  uint32_t n, i;

  /*
   * Find the index of the last problem clause:
   *   cidx = 0 if there are no problem clauses
   *   cidx = pool->size if there are less problem clauses than expected
   */
  n = pool->num_prob_clauses;
  cidx = 0;
  end = 0;
  for (i=0; i<n; i++) {
    cidx = next_clause_index(pool, end);
    if (cidx >= pool->size) break;
    end = cidx + clause_full_length(pool, cidx);
  }

  if (cidx == pool->size) {
    fprintf(stderr, "**** BUG: expected %"PRIu32" problem clauses. Found %"PRIu32". ****\n", 
	    pool->num_prob_clauses, i + 1);
    fflush(stderr);
  } else {
    next = next_clause_index(pool, end);        // next clause after that (i.e., first learned clause or nothing)
    if (cidx >= pool->learned) {
      fprintf(stderr, "**** BUG: last problem clause starts at %"PRIu32". Learned index is %"PRIu32" ****\n",
	      cidx, pool->learned);
      fflush(stderr);
    } else if (end > pool->learned) {
      fprintf(stderr, "**** BUG: last problem clause ends at %"PRIu32". Learned index is %"PRIu32" ****\n",
	      end, pool->learned);
      fflush(stderr);
    } else if (next < pool->size && next < pool->learned) {
      fprintf(stderr, "**** BUG: first learned clause starts at %"PRIu32". Learned index is %"PRIu32" ****\n",
	      next, pool->learned);
      fflush(stderr);
    }
  }
}



/*
 * HEAP INVARIANTS
 */
static void check_heap(const var_heap_t *heap) {
  uint32_t i, j, n;
  int32_t k;
  bvar_t x, y;

  n = heap->heap_last;
  for (i=0; i<=n; i++) {
    x = heap->heap[i];
    if (heap->heap_index[x] != (int32_t) i) {
      fprintf(stderr, "*** BUG: heap[%"PRIu32"] = %"PRIu32" but heap_index[%"PRIu32"] = %"PRId32" ****\n",
	      i, x, x, heap->heap_index[x]);
    }
    j = i>>1; // parent of i (or j=i=0 for the special marker)
    y = heap->heap[j];
    if (heap->activity[y] < heap->activity[x]) {
      fprintf(stderr, "*** BUG: bad heap ordering: activity[%"PRIu32"] < activity[%"PRIu32"] ****\n", j, i);
    }
  }

  n = heap->size;
  for (i=0; i<n; i++) {
    k= heap->heap_index[i];
    if (k >= 0 && heap->heap[k] != i) {
      fprintf(stderr, "*** BUG: heap_index[%"PRIu32"] = %"PRId32" but heap[%"PRId32"] = %"PRIu32" ****\n",
	      i, k, k, heap->heap[k]);
    }
  }
}


/*
 * SORTING FOR CLAUSE DELETION
 * - a = array of clause idx
 * - n = number of elements in a
 * We check that all elements in a can be deleted and that a is sorted in increasing order.
 */
static void check_candidate_clauses_to_delete(const sat_solver_t *solver, const cidx_t *a, uint32_t n) {
  uint32_t i;
  cidx_t c1, c2;
  float a1, a2;

  for (i=0; i<n; i++) {
    c1 = a[i];
    if (clause_is_locked(solver, c1)) {
      fprintf(stderr, "**** BUG: locked clause (cidx = %"PRIu32") is candidate for deletion ****\n", c1);
      fflush(stderr);
    }
  }

  if (n <= 1) return;

  c1 = a[0];
  a1 = get_learned_clause_activity(&solver->pool, c1);
  for (i=1; i<n; i++) {
    c2 = a[i];
    a2 = get_learned_clause_activity(&solver->pool, c2);
    if (a1 > a2 || (a1 == a2 && c1 > c2)) {
      fprintf(stderr, "**** BUG: candidates for deletion not sorted (at position i = %"PRIu32")\n", i);
      fflush(stderr);
    }
    a1 = a2;
    c1 = c2;
  }
}


/*
 * WATCH VECTORS
 */

/*
 * Check that cidx occurs in vector watch[l]
 */
static bool clause_is_in_watch_vector(const sat_solver_t *solver, literal_t l, cidx_t cidx) {
  const watch_t *w;
  uint32_t i, n;

  w = solver->watch[l];
  if (w != NULL) {
    n = w->size;
    i = 0;
    while (i < n) {
      if (idx_is_literal(w->data[i])) {
	i ++;
      } else {
	if (w->data[i] == cidx) {
	  return true;
	}
	i += 2;
      }
    }
  }

  return false;
}

static void check_all_clauses_are_in_watch_vectors(const sat_solver_t *solver) {
  cidx_t cidx, end;
  literal_t l0, l1;

  cidx = clause_pool_first_clause(&solver->pool);
  end = solver->pool.size;

  while (cidx < end) {
    l0 = first_literal_of_clause(&solver->pool, cidx);
    l1 = second_literal_of_clause(&solver->pool, cidx);
    assert(l0 < solver->nliterals && l1 < solver->nliterals);
    if (!clause_is_in_watch_vector(solver, l0, cidx)) {
      fprintf(stderr, "*** BUG: missing clause index (%"PRIu32") in watch vector for literal %"PRIu32" ***\n",
	      cidx, l0);
      fflush(stderr);
    }
    if (!clause_is_in_watch_vector(solver, l1, cidx)) {
      fprintf(stderr, "*** BUG: missing clause index (%"PRIu32") in watch vector for literal %"PRIu32" ***\n",
	      cidx, l1);
      fflush(stderr);
    }
    cidx = clause_pool_next_clause(&solver->pool, cidx);
  }
}

static void check_watch_vector_is_good(const sat_solver_t *solver, const watch_t *w, literal_t l) {
  uint32_t i, n, k;

  assert(w != NULL && w == solver->watch[l]);

  n = w->size;
  i = 0;
  while (i < n) {
    k = w->data[i];
    if (idx_is_clause(k)) {
      if (first_literal_of_clause(&solver->pool, k) != l &&
	  second_literal_of_clause(&solver->pool, k) != l) {
	fprintf(stderr, "*** BUG: clause %"PRIu32" is in watch vector for literal %"PRIu32"\n, but the literal is not first or second ***\n", k, l);
	fflush(stderr);
      }
      i += 2;
    } else {
      i ++;
    }
  }
}

static void check_all_watch_vectors_are_good(const sat_solver_t *solver) {
  uint32_t i, n;
  watch_t *w;

  n = solver->nliterals;
  for (i=0; i<n; i++) {
    w = solver->watch[i];
    if (w != NULL) {
      check_watch_vector_is_good(solver, w, i);
    }
  }
}

static void check_watch_vectors(const sat_solver_t *solver) {
  check_all_clauses_are_in_watch_vectors(solver);
  check_all_watch_vectors_are_good(solver);
}


/*
 * PROPAGATION
 */

/*
 * Check whether clause cidx is true
 */
static bool clause_is_true(const sat_solver_t *solver, cidx_t cidx) {
  uint32_t i, n;
  literal_t *lit;

  assert(good_clause_idx(&solver->pool, cidx));

  n = clause_length(&solver->pool, cidx);
  lit = clause_literals(&solver->pool, cidx);
  for (i=0; i<n; i++) {
    if (lit_is_true(solver, lit[i])) {
      return true;
    }
  }

  return false;
}


/*
 * Get the number of false literals in clause cidx
 */
static uint32_t num_false_literals_in_clause(const sat_solver_t *solver, cidx_t cidx) {
  uint32_t i, n, cnt;
  literal_t *lit;

  assert(good_clause_idx(&solver->pool, cidx));

  n = clause_length(&solver->pool, cidx);
  lit = clause_literals(&solver->pool, cidx);
  cnt = 0;
  for (i=0; i<n; i++) {
    if (lit_is_false(solver, lit[i])) {
      cnt ++;
    }
  }

  return cnt;
}

/*
 * Check that no propagation was missed (for the clause pool)
 * - this is called when there's no conflict reported
 */
static void check_pool_propagation(const sat_solver_t *solver) {
  cidx_t cidx;
  uint32_t f, n;

  for (cidx = clause_pool_first_clause(&solver->pool);
       cidx < solver->pool.size;
       cidx = clause_pool_next_clause(&solver->pool, cidx)) {
    if (! clause_is_true(solver, cidx)) {
      f = num_false_literals_in_clause(solver, cidx);
      n = clause_length(&solver->pool, cidx);
      if (f == n) {
	fprintf(stderr, "*** BUG: missed conflict. Clause %"PRIu32" is false ***\n", cidx);
	fflush(stderr);
      } else if (f == n -1) {
	fprintf(stderr, "*** BUG: missed propagation for clause %"PRIu32" ***\n", cidx);
	fflush(stderr);
      }
    }
  }
}


/*
 * Report missed conflicts and propagation for vector w
 * - l = literal corresponding to w (i.e., solver->watch[l] is w)
 * - l is false in the solver.
 */
static void check_missed_watch_prop(const sat_solver_t *solver, const watch_t *w, literal_t l) {
  uint32_t i, k, n;
  literal_t l1;

  assert(lit_is_false(solver, l) && solver->watch[l] == w);

  n = w->size;
  i = 0;
  while (i < n) {
    k = w->data[i];
    if (idx_is_literal(k)) {
      l1 = idx2lit(k);
      if (lit_is_false(solver, l1)) {
	fprintf(stderr, "*** BUG: missed binary conflict for clause %"PRIu32" %"PRIu32" ***\n", l, l1);
	fflush(stderr);
      } else if (lit_is_unassigned(solver, l1)) {
	fprintf(stderr, "*** BUG: missed binary propagation for clause %"PRIu32" %"PRIu32" ***\n", l, l1);
	fflush(stderr);
      }
      i ++;
    } else {
      i += 2;
    }
  }
}


/*
 * Check that no propagation was missed (for the binary clauses)
 * - this is called when no conflict was reported
 */
static void check_binary_propagation(const sat_solver_t *solver) {
  uint32_t i, n;
  const watch_t *w;

  n = solver->nliterals;
  for (i=0; i<n; i++) {
    if (lit_is_false(solver, i)) {
      w = solver->watch[i];
      if (w != NULL) {
	check_missed_watch_prop(solver, w, i);
      }
    }
  }
}


/*
 * Check that all literals implied by a clause cidx are in first
 * position in that clause.
 */
static void check_clause_antecedents(const sat_solver_t *solver) {
  uint32_t i;
  literal_t l;
  cidx_t cidx;

  for (i=0; i<solver->stack.top; i++) {
    l = solver->stack.lit[i];
    if (solver->ante_tag[var_of(l)] == ATAG_CLAUSE) {
      cidx = solver->ante_data[var_of(l)];
      if (first_literal_of_clause(&solver->pool, cidx) != l) {
	fprintf(stderr, "*** BUG: implied literal %"PRIu32" is not first in clause %"PRIu32" ****\n", l, cidx);
	fflush(stderr);
      }
    }
  }
}


/*
 * Check that all propagations are sound:
 * - in a binary propagation {l, l1} then l1 must be false
 * - in a clause propagation {l, l1 .... l_k} then l1 ... l_k must all be false
 */
static void check_sound_propagation(const sat_solver_t *solver) {
  uint32_t i, n, f;
  cidx_t cidx;
  literal_t l, l1;

  for (i=0; i<solver->stack.top; i++) {
    l = solver->stack.lit[i];
    assert(lit_is_true(solver, l));
    switch (solver->ante_tag[var_of(l)]) {
    case ATAG_BINARY:
      l1 = solver->ante_data[var_of(l)];
      if (! lit_is_false(solver, l1)) {
	fprintf(stderr, "*** BUG: unsound propgation for binary clause %"PRIu32" %"PRIu32" ***\n", l, l1);
	fflush(stderr);
      }
      break;

    case ATAG_CLAUSE:
      cidx = solver->ante_data[var_of(l)];
      f = num_false_literals_in_clause(solver, cidx);
      n = clause_length(&solver->pool, cidx);
      if (f != n - 1) {
	fprintf(stderr, "*** BUG: unsound propagation. Clause %"PRIu32" antecedent of literal %"PRIu32" ***\n",
		cidx, l);
	fflush(stderr);
      }
      break;

    default:
      break;
    }
  }
}

/*
 * Full check
 */
static void check_propagation(const sat_solver_t *solver) {  
  check_binary_propagation(solver);
  check_pool_propagation(solver);
  check_clause_antecedents(solver);
  check_sound_propagation(solver);
}


/*******************************
 *  MARKS AND LEARNED CLAUSES  *
 ******************************/

/*
 * Check that all literals in solver->buffer are marked
 */
static void check_buffer_marks(const sat_solver_t *solver) {
  uint32_t n, i;
  literal_t l;

  n = solver->buffer.size;
  for (i=0; i<n; i++) {
    l = solver->buffer.data[i];
    if (! variable_is_marked(solver, var_of(l))) {
      fprintf(stderr, "*** BUG: literal %"PRIu32" in the learned clause is not marked ***\n", l);
      fflush(stderr);
    }
  }
}

/*
 * Count the number of marked variables
 */
static uint32_t num_marked_variables(const sat_solver_t *solver) {
  uint32_t n, i, c;

  c = 0;
  n = solver->nvars;
  for (i=0; i<n; i++) {
    if (variable_is_marked(solver, i)) {
      c ++;
    }
  }

  return c;
}


/*
 * After construction of the learned clause (before it's simplified):
 * - all literals in the clause must be marked.
 * - no other literals should be marked.
 */
static void check_marks(const sat_solver_t *solver) {
  uint32_t n;

  n = num_marked_variables(solver);
  if (n != solver->buffer.size) {
    fprintf(stderr, "*** BUG: expected %"PRIu32" marked variables; found %"PRIu32" ***\n",
	    solver->buffer.size, n);
  } else {
    check_buffer_marks(solver);
  }
}


/*
 * When we've simplified the learned clause: no variable should be marked
 */
static void check_all_unmarked(const sat_solver_t *solver) {
  uint32_t n;

  n = num_marked_variables(solver);
  if (n > 0) {
    fprintf(stderr, "*** BUG: found %"PRIu32" marked variables: should be 0 ***\n", n);
    fflush(stderr);
  }
}


#endif
