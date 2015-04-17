/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "solvers/simplex/offset_equalities.h"
#include "utils/hash_functions.h"
#include "utils/index_vectors.h"
#include "utils/int_partitions.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"



#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * GLOBAL COUNTER: INCREMENTED AFTER EVERY TEST
 */
static uint32_t ctr = 0;

/*
 * TABLE OF POLYNOMIALS
 */

/*
 * - poly[0] is not used
 * - poly[i] may be NULL (this means that xi is a variable)
 *   or poly[i] is a polynomial that depend on variables with index < i
 * - vars = array of all indices such that poly[i] = NULL
 */
typedef struct poly_table_s {
  uint32_t psize;    // size of the poly array
  uint32_t npolys;   // current number of elements in poly (i.e., poly[1 ... npolys-1] are defined)
  polynomial_t **poly;

  uint32_t vsize;    // size of the var arrey
  uint32_t nvars;     // number of variabels stored in vars
  int32_t *var;
} poly_table_t;

#define MAX_PSIZE (UINT32_MAX/sizeof(polynomial_t *))
#define MAX_VSIZE (UINT32_MAX/sizeof(int32_t))



/*
 * Initialize: np = initial psize, nv = initial vsize
 */
static void init_poly_table(poly_table_t *table, uint32_t np, uint32_t nv) {
  assert(0 < np && np <= MAX_PSIZE && nv <= MAX_VSIZE);

  table->psize = np;
  table->npolys = 1;
  table->poly = (polynomial_t **) safe_malloc(np * sizeof(polynomial_t *));
  table->poly[0] = NULL; // not used

  table->vsize = nv;
  table->nvars = 0;
  table->var = (int32_t *) safe_malloc(nv * sizeof(int32_t));
}


/*
 * Increase the array's sizes
 */
static void make_room_for_polys(poly_table_t *table) {
  uint32_t n;

  n = 2 * table->psize;
  if (n > MAX_PSIZE) {
    out_of_memory();
  }
  table->poly = (polynomial_t **) safe_realloc(table->poly, n * sizeof(polynomial_t *));
  table->psize  = n;
}

static void make_room_for_vars(poly_table_t *table) {
  uint32_t n;

  n = 2 * table->vsize;
  if (n > MAX_VSIZE) {
    out_of_memory();
  }
  table->var = (int32_t *) safe_realloc(table->var, n * sizeof(int32_t));
  table->vsize = n;
}


/*
 * Add i to the variable array
 */
static void add_var(poly_table_t *table, int32_t i) {
  uint32_t j;

  j = table->nvars;
  if (j == table->vsize) {
    make_room_for_vars(table);
  }
  assert(j < table->vsize);
  table->var[j] = i;
  table->nvars = j+1;
}

/*
 * Add polynomial p to the table
 * - stores p in table->poly[i].
 * - if p is NULL, also add i to the variable array
 */
static void add_poly(poly_table_t *table, polynomial_t *p) {
  uint32_t i;

  i = table->npolys;
  if (i == table->psize) {
    make_room_for_polys(table);
  }
  assert(i < table->psize);
  table->poly[i] = p;
  table->npolys = i+1;

  if (p == NULL) {
    add_var(table, i);
  }
}


/*
 * Delete the arrays
 */
static void delete_poly_table(poly_table_t *table) {
  polynomial_t *p;
  uint32_t i, n;

  n = table->npolys;
  for (i=1; i<n; i++) {
    p = table->poly[i];
    if (p != NULL) {
      free_polynomial(p);
    }
  }

  safe_free(table->poly);
  safe_free(table->var);
  table->poly = NULL;
  table->var = NULL;
}




/*
 * RANDOM POLYNOMIALS
 */

/*
 * - coeff[0 .. NCOEFF] define the coefficients and their distribution
 * - nterms[0 .. NTERMS] define the number of terms
 * - constant[0 .. NCONST]: constant parts
 * - we favor small polynomials with coefficients +1/-1
 */

#define NCOEFF 20
#define NTERMS 12
#define NCONST 40

static const int32_t coeff[NCOEFF] = {
  1, 1, 1, 1,
  -1, -1, -1, -1,
  2, 2, -2, -2,
  3, 4, 7, 8,
  -3, -4, -7, -8,
};

static const uint32_t nterms[NTERMS] = {
  0, 1, 1, 2, 2, 2,
  3, 3, 3, 5, 10, 20,
};

static const int32_t constant[NCONST] = {
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
  0, -1, -2, -3, -4, -5, -6, -7, -8. -9,
  0, 0, 0, 10, 20, 30, 40, 50, 100, 200,
  0, 0, 0, -10, -20, -30, -40, -50, -100, -200,
};


// random integer in [0 ... n-1]
static inline uint32_t random_index(uint32_t n) {
  assert(n > 0);
  return ((uint32_t) random()) % n;
}

static inline int32_t random_coeff(void) {
  return coeff[random_index(NCOEFF)];
}

static inline uint32_t random_nterms(void) {
  return nterms[random_index(NTERMS)];
}

static inline int32_t random_constant(void) {
  return constant[random_index(NCONST)];
}


/*
 * Random variable in table
 */
static inline int32_t random_var(poly_table_t *table) {
  return table->var[random_index(table->nvars)];
}


/*
 * Random polynomial:
 * - use variables defined in table
 */
static polynomial_t *random_poly(poly_buffer_t *b, poly_table_t *table) {
  rational_t q;
  uint32_t i, n;
  int32_t x, a;

  q_init(&q);
  reset_poly_buffer(b);

  a = random_constant();
  q_set32(&q, a);
  poly_buffer_add_const(b, &q);

  n = random_nterms();
  for (i=0; i<n; i++) {
    a = random_coeff();
    x = random_var(table);
    assert(x > 0);

    q_set32(&q, a);
    poly_buffer_add_monomial(b, x, &q);
  }

  normalize_poly_buffer(b);
  q_clear(&q);

  return poly_buffer_get_poly(b);
}


/*
 * Fill table with random polys:
 * - nvars = number of initial variables (must be positive)
 *   poly[1 ... nvars] will all be variables
 * - n = total number of polynomials to build (including nvars)
 */
static void build_poly_table(poly_table_t *table, uint32_t nvars, uint32_t n) {
  poly_buffer_t buffer;
  polynomial_t *p;
  uint32_t i;

  for (i=0; i<nvars; i++) {
    add_poly(table, NULL);
  }

  init_poly_buffer(&buffer);

  while (i<n) {
    p = NULL;
    if (random_index(10) != 0) {
      p = random_poly(&buffer, table);
    }
    add_poly(table, p);
    i ++;
  }

  delete_poly_buffer(&buffer);
}



/*
 * SUBSTITUTIONS
 */

/*
 * To double check the offset manager results, we store a variable
 * substitution in the following data structure.
 * - subst->size = an upper bound on the actual number of varibles
 * - subst->elim[x] = true if x is mapped to (y + k) in the substitution
 * - subst->var[x] = the variable y
 * - subst->delta[x] = the constant k
 *
 * Special encoding: mapping x := k is stored by setting var[x] = -1, delta[x] = k
 */
typedef struct substitution_s {
  uint32_t size;
  uint8_t *elim;
  int32_t *var;
  int32_t *delta;
} substitution_t;

#define MAX_SUBSTITUTION_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Pair variable, offset (result of substitution applied to an x)
 */
typedef struct offset_pair_s {
  int32_t var;
  int32_t delta;
} offset_pair_t;


/*
 * Offset equality descriptor: for x = y + offset
 */
typedef struct offset_equality_s {
  int32_t lhs; // x
  int32_t rhs; // y
  int32_t offset;
} offset_equality_t;



/*
 * Initialize for n variables
 */
static void init_substitution(substitution_t *s, uint32_t n) {
  uint32_t i;

  assert(n <= MAX_SUBSTITUTION_SIZE);

  s->size = n;
  s->elim = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  s->var = (int32_t *) safe_malloc(n * sizeof(int32_t));
  s->delta = (int32_t *) safe_malloc(n * sizeof(int32_t));

  for (i=0; i<n; i++) {
    s->elim[i] = false;
  }
}


/*
 * Delete
 */
static void delete_substitution(substitution_t *s) {
  safe_free(s->elim);
  safe_free(s->var);
  safe_free(s->delta);
  s->elim = NULL;
  s->var = NULL;
  s->delta = NULL;
}


/*
 * Add x := y + k to s
 * - x must not be mapped already
 */
static void add_subst(substitution_t *s, int32_t x, int32_t y, int32_t k) {
  assert(0 < x && x < s->size && -1 <= y && y < (int32_t) s->size && !s->elim[x]);
  s->elim[x] = true;
  s->var[x] = y;
  s->delta[x] = k;
}


/*
 * Remove the mapping of x
 */
static void remove_subst(substitution_t *s, int32_t x) {
  assert(0 < x && x < s->size && s->elim[x]);
  s->elim[x] = false;
}



/*
 * Apply the subsitution to a pair d = x + k
 */
static void subst_var(substitution_t *s, offset_pair_t *d) {
  uint32_t n;
  int32_t x;
  int32_t k;

  n = s->size; // to detect circularities

  x = d->var;
  k = d->delta;

  assert(x < (int32_t) s->size);
  while (x >= 0 && s->elim[x]) {
    k += s->delta[x];
    x = s->var[x];
    n --;
    if (n == 0) goto bug;
    assert(x < (int32_t) s->size);
  }

  d->var = x;
  d->delta = k;

  return;

 bug:
  fprintf(stderr, "*** BUG: circular substitution detected ***\n");
  exit(1);
}


/*
 * Apply s to an offset equality x = y + offset
 */
static void subst_eq(substitution_t *s, offset_equality_t *e) {
  offset_pair_t aux1, aux2;

  aux1.var = e->lhs;
  aux1.delta = 0;
  subst_var(s, &aux1);

  aux2.var = e->rhs;
  aux2.delta = 0;
  subst_var(s, &aux2);

  e->lhs = aux1.var;
  e->rhs = aux2.var;
  e->offset -= aux1.delta;
  e->offset += aux2.delta;
}


/*
 * Apply s to a monomial array mono
 * - store the result in buffer b
 */
static void subst_poly(substitution_t *s, poly_buffer_t *b, monomial_t *mono) {
  offset_pair_t aux;
  rational_t q;
  int32_t x;

  q_init(&q);
  reset_poly_buffer(b);

  x = mono->var;
  while (x != max_idx) {
    if (x == const_idx) {
      poly_buffer_add_const(b, &mono->coeff);
    } else {
      aux.var = x;
      aux.delta = 0;
      subst_var(s, &aux); // aux constains S[x] = y + delta

      // add a * y + a * delta to b
      if (aux.var > 0) {
	poly_buffer_add_monomial(b, aux.var, &mono->coeff);
      }
      q_set32(&q, aux.delta);
      poly_buffer_addmul_monomial(b, const_idx, &mono->coeff, &q);
    }
    mono ++;
    x = mono->var;
  }

  normalize_poly_buffer(b);
  q_clear(&q);
}


/*
 * Apply s to poly[i]
 * - store the result in buffer b
 */
static void subst_poly_idx(substitution_t *s, poly_table_t *table, poly_buffer_t *b, int32_t i) {
  monomial_t aux[2];
  polynomial_t *p;

  assert(0 < i && i < table->npolys);
  p = table->poly[i];
  if (p == NULL) {
    // build the polynomial 1.i in aux
    aux[0].var = i;
    q_init(&aux[0].coeff);
    q_set_one(&aux[0].coeff);
    aux[1].var = max_idx;
    subst_poly(s, b, aux);
    q_clear(&aux[0].coeff);
  } else {
    subst_poly(s, b, p->mono);
  }
}



/*
 * NORMAL FORM OF A POLYNOMIAL
 */

/*
 * For a polynomial p and a subsitution s, the normal form of p is s(p)
 * - we store the result in the following structure:
 *   nterms = number of terms in s(p)
 *   mono   = the monmoials of s(p)
 *   hash   = hash code for the s(p)
 * - the size of array mono must be set to nterms(p) + 2 initially
 */
typedef struct normal_form_s {
  uint32_t hash;
  uint32_t nterms;
  uint32_t size;
  monomial_t mono[0];
} normal_form_t;


/*
 * allocate a normal_form buffer with n monomials + one end marker
 * - the rational coefficients in mono[0 ... n-1] are all initialized
 * - mono[n] is allocated but not initialized
 */
static normal_form_t *new_normal_form(uint32_t n) {
  normal_form_t *tmp;
  uint32_t i;

  assert(n < 1000);

  tmp = (normal_form_t *) safe_malloc(sizeof(normal_form_t) + (n + 1) * sizeof(monomial_t));
  tmp->size = n;
  for (i=0; i<n; i++) {
    q_init(&tmp->mono[i].coeff);
  }

  return tmp;
}

static void free_normal_form(normal_form_t *tmp) {
  uint32_t i, n;

  n = tmp->size;
  for (i=0; i<n; i++) {
    q_clear(&tmp->mono[i].coeff);
  }
  safe_free(tmp);
}

/*
 * Copy the content of buffer b into f
 */
static void set_normal_form(normal_form_t *f, poly_buffer_t *b) {
  monomial_t *mono;
  uint32_t i, n;

  n = poly_buffer_nterms(b);
  mono = poly_buffer_mono(b);

  assert(n <= f->size);
  for (i=0; i<n; i++) {
    f->mono[i].var = mono[i].var;
    q_set(&f->mono[i].coeff, &mono[i].coeff);
  }
  f->mono[i].var = max_idx; // end marker

  f->nterms = n;
  f->hash = hash_monarray(f->mono, n);
}


/*
 * Check whether f and g are equal
 */
static bool equal_normal_forms(normal_form_t *f, normal_form_t *g) {
  return f->hash == g->hash && f->nterms == g->nterms && equal_monarrays(f->mono, g->mono);
}



/*
 * RESULTS FROM THE OFFSET MANAGER
 */

/*
 * The offset manager propagates equalities between two variables x and y
 * - both x and y are variables in a poly_table
 * - we store the equalities we get in a stack
 *   we also store the rx = root of x and ry = root of y
 * - to mark backtracking point, we use a fake equality -1 == -1
 * - we also use a merge table to compute equivalence classes
 */
typedef struct equality_s {
  int32_t lhs;  // x
  int32_t rhs;  // y
  int32_t root_lhs; // rx
  int32_t root_rhs; // ry
} equality_t;

typedef struct equality_queue_s {
  uint32_t qsize;
  uint32_t top;
  equality_t *data;

  uint32_t nvars;
  int32_t *parent; // array of nvars elements
} equality_queue_t;

#define MAX_QSIZE (UINT32_MAX/sizeof(equality_t))



/*
 * Initialize the queue
 * - n = number of variables
 */
static void init_equality_queue(equality_queue_t *queue, uint32_t n) {
  uint32_t i;

  queue->qsize = 1000;
  queue->top = 0;
  queue->data = (equality_t *) safe_malloc(1000 * sizeof(equality_t));

  queue->nvars = n;
  queue->parent = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    queue->parent[i] = i;
  }
}


/*
 * Make room for more equalities
 */
static void extend_equality_queue(equality_queue_t *queue) {
  uint32_t n;

  n = 2 * queue->qsize;
  if (n > MAX_QSIZE) {
    out_of_memory();
  }

  queue->data = (equality_t *) safe_realloc(queue->data, n * sizeof(equality_t));
  queue->qsize = n;
}


/*
 * Delete
 */
static void delete_equality_queue(equality_queue_t *queue) {
  safe_free(queue->data);
  safe_free(queue->parent);
  queue->data = NULL;
  queue->parent = NULL;
}


/*
 * Root of x in queue->parent tree
 */
static int32_t root_of_var(equality_queue_t *queue, int32_t x) {
  int32_t p;

  do {
    assert(0 <= x && x < queue->nvars);
    p = x;
    x = queue->parent[x];
  } while (p != x);

  return p;
}


#if 0
/*
 * Check whether x is a root in the equivalence classes
 */
static bool var_is_root(equality_queue_t *queue, int32_t x) {
  assert(0 <= x && x < queue->nvars);
  return queue->parent[x] == x;
}
#endif


/*
 * Add equality x == y to the queue:
 */
static void push_equality(equality_queue_t *queue, int32_t x, int32_t y) {
  uint32_t i;
  int32_t rx, ry;

  rx = root_of_var(queue, x);
  ry = root_of_var(queue, y);

  i = queue->top;
  if (i == queue->qsize) {
    extend_equality_queue(queue);
  }
  assert(i < queue->qsize);

  queue->data[i].lhs = x;
  queue->data[i].rhs = y;
  queue->data[i].root_lhs = rx;
  queue->data[i].root_rhs = ry;

  queue->top = i+1;

  // update the parents: we always do lhs := rhs (so ry stays root)
  // this is a no-op if rx = ry (as we want).
  queue->parent[rx] = ry;
}


/*
 * Add a backtrack mark to the queue
 */
static void push_mark(equality_queue_t *queue) {
  uint32_t i;

  i = queue->top;
  if (i == queue->qsize) {
    extend_equality_queue(queue);
  }
  assert(i < queue->qsize);
  queue->data[i].lhs = -1;
  queue->data[i].rhs = -1;
  queue->data[i].root_lhs = -1;
  queue->data[i].root_rhs = -1;

  queue->top = i+1;
}


/*
 * Backtrack to the top-most mark
 * - if there's no mark, empty the queue
 */
static void equality_queue_backtrack(equality_queue_t *queue) {
  uint32_t i;
  int32_t rx;

  i = queue->top;
  while (i > 0) {
    i --;
    if (queue->data[i].lhs < 0) break; // marker
    // restore parent
    rx = queue->data[i].root_lhs;
    assert(0 <= rx && rx < queue->nvars &&
	   queue->parent[rx] == queue->data[i].root_rhs);
    queue->parent[rx] = rx;
  }

  queue->top = i;
}


/*
 * Call back: report that x and y are equal
 * - aux is a pointer to an equality queue
 * - x and y must be two variable indices in this table
 */
static void notify_equality(void *aux, int32_t x, int32_t y) {
  equality_queue_t *queue;

  queue = aux;
  assert(1 <= x && x <= queue->nvars && 0 <= y && y <= queue->nvars);
  printf("[%"PRIu32"]: Received equality: x%"PRId32" == x%"PRId32"\n", ctr, x, y);
  if (root_of_var(queue, x) == root_of_var(queue, y)) {
    printf("---> redundant\n");
  }
  fflush(stdout);

  push_equality(queue, x, y);
}


/*
 * Equivalence classes defined by queue->parent
 */
// test equivalence (callbacks for ipart: aux is an equality queue)
static bool prop_same_class(void *aux, int32_t x, int32_t y) {
  equality_queue_t *queue;

  queue = aux;
  return root_of_var(queue, x) == root_of_var(queue, y);
}

// hash code
static uint32_t prop_hash_var(void * aux, int32_t x) {
  equality_queue_t *queue;

  queue = aux;
  return jenkins_hash_int32(root_of_var(queue, x));
}


static void collect_propagated_classes(equality_queue_t *queue, ipart_t *partition) {
  uint32_t i, n;

  n = queue->nvars;
  for (i=0; i<n; i++) {
    int_partition_add(partition, i);
  }
}



/*
 * TEST BENCH
 */

/*
 * Active polynomials:
 * - a polynomial i is active if it was added to the offset manager
 * - there are npolys active polynomials
 * - for each i in 0 ... npolys - 1
 * - id[i] = index in the relevant poly_table
 * - norm[i] = normal form for the polynomial
 * - also when we add activate polynomial k, we mark active[k] = true
 */
typedef struct active_poly_table_s {
  uint32_t size;   // size of arrays id and norm
  uint32_t npolys; // number of active polys stored
  int32_t *id;
  normal_form_t **norm;
  uint8_t *active;
} active_poly_table_t;

#define MAX_ACTIVE_POLYS (UINT32_MAX/sizeof(normal_form_t *))

// m = fixed size of the active poly table
static void init_active_polys(active_poly_table_t *table, uint32_t n) {
  uint32_t i;

  assert(n <= MAX_ACTIVE_POLYS);

  table->size = n;
  table->npolys = 0;
  table->id = (int32_t *) safe_malloc(n * sizeof(int32_t));
  table->norm = (normal_form_t **) safe_malloc(n * sizeof(normal_form_t *));
  table->active = (uint8_t *) safe_malloc(n * sizeof(uint8_t));

  for (i=0; i<n; i++) {
    table->active[i] = false;
  }
}

static void delete_active_polys(active_poly_table_t *table) {
  uint32_t i, n;

  n = table->npolys;
  for (i=0; i<n; i++) {
    free_normal_form(table->norm[i]);
  }
  safe_free(table->id);
  safe_free(table->norm);
  safe_free(table->active);
  table->id = NULL;
  table->norm = NULL;
  table->active = NULL;
}

static void add_active_poly(active_poly_table_t *table, poly_table_t *ptbl, int32_t i) {
  polynomial_t *p;
  normal_form_t *q;
  uint32_t k, n;

  assert(0 < i && i < ptbl->npolys && !table->active[i]);

  p = ptbl->poly[i];
  n = (p == NULL) ? 2 : (p->nterms + 1);
  q = new_normal_form(n);

  k = table->npolys;
  assert(k < table->size);
  table->id[k] = i;
  table->norm[k] = q;
  table->npolys = k + 1;

  table->active[i] = true;
}

static void remove_active_poly(active_poly_table_t *table) {
  uint32_t k;
  int32_t id;

  assert(table->npolys > 0);

  k = table->npolys - 1;
  free_normal_form(table->norm[k]);
  id = table->id[k];

  assert(table->active[id]);
  table->active[id] = false;

  table->npolys = k;
}


/*
 * Substitution queue
 * - to undo/update the substitution, we keep track of variable
 * - when we add x:= y + k to subst, we store x at the end of the variable queue
 * - to mark backtrack point, we store -1 at the top of the queue
 */
typedef struct subst_queue_s {
  uint32_t size;
  uint32_t top;
  int32_t *data;
} subst_queue_t;

#define MAX_SQUEUE_SIZE (UINT32_MAX/sizeof(int32_t))

// n = initial size
static void init_subst_queue(subst_queue_t *queue, uint32_t n) {
  assert(n <= MAX_SQUEUE_SIZE);
  queue->size = n;
  queue->top = 0;
  queue->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
}

static void delete_subst_queue(subst_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}

static void extend_subst_queue(subst_queue_t *queue) {
  uint32_t n;

  n = 2 * queue->size;
  if (n > MAX_SQUEUE_SIZE) {
    out_of_memory();
  }
  queue->data = (int32_t *) safe_realloc(queue->data, n * sizeof(int32_t));
  queue->size = n;
}

static void subst_queue_push_item(subst_queue_t *queue, int32_t x) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_subst_queue(queue);
  }
  assert(i < queue->size);
  queue->data[i] = x;
  queue->top = i+1;
}

static inline void subst_queue_push_var(subst_queue_t *queue, int32_t x) {
  assert(x >= 0);
  subst_queue_push_item(queue, x);
}

static inline void subst_queue_push_mark(subst_queue_t *queue) {
  subst_queue_push_item(queue, -1);
}



/*
 * Queue of test operations
 * - operations on offset_manager include
 *   record_poly
 *   assert_eq
 *   propagate
 *   increase_dlevel
 *   backtrack
 *   push
 *   pop
 * - for testing we keep track of the sequence of operations
 *   performed (except push and backtrack)
 * - desciptors for each operation:
 *   record_poly(i): activate polynomial of index i
 *
 */
typedef enum operations {
  RECORD_POLY,
  ASSERT_EQ,
  PROPAGATE,
  INCREASE_DLEVEL,
  PUSH,
} operation_t;

typedef struct op_desc_s {
  operation_t tag;
  union {
    int32_t rec_id;        // argument of RECORD_POLY
    offset_equality_t eq;  // argument of ASSERT_EQ
  } arg;
} op_desc_t;

typedef struct op_stack_s {
  uint32_t size;
  uint32_t top;
  op_desc_t *data;
} op_stack_t;

#define MAX_OP_STACK_SIZE (UINT32_MAX/sizeof(op_desc_t))

static void init_op_stack(op_stack_t *stack) {
  uint32_t n;

  n = 100;
  stack->size = n;
  stack->top = 0;
  stack->data = (op_desc_t *) safe_malloc(n * sizeof(op_desc_t));
}

static void extend_op_stack(op_stack_t *stack) {
  uint32_t n;

  n = stack->size * 2;
  if (n > MAX_OP_STACK_SIZE) {
    out_of_memory();
  }
  stack->size = n;
  stack->data = (op_desc_t *) safe_realloc(stack->data, n * sizeof(op_desc_t));
}

static void delete_op_stack(op_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}

static void push_record_poly(op_stack_t *stack, int32_t id) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_op_stack(stack);
  }
  assert(i < stack->size);

  stack->data[i].tag = RECORD_POLY;
  stack->data[i].arg.rec_id = id;
  stack->top = i+1;
}

static uint32_t push_assert_eq(op_stack_t *stack, int32_t x, int32_t y, int32_t offset) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_op_stack(stack);
  }
  assert(i < stack->size);

  stack->data[i].tag = ASSERT_EQ;
  stack->data[i].arg.eq.lhs = x;
  stack->data[i].arg.eq.rhs = y;
  stack->data[i].arg.eq.offset = offset;
  stack->top = i+1;

  return i;
}

static void push_op(op_stack_t *stack, operation_t op) {
  uint32_t i;

  assert(op == PROPAGATE || op == PUSH || op == INCREASE_DLEVEL);

  i = stack->top;
  if (i == stack->size) {
    extend_op_stack(stack);
  }
  assert(i < stack->size);

  stack->data[i].tag = op;
  stack->top = i+1;
}

static inline void push_propagate(op_stack_t *stack) {
  push_op(stack, PROPAGATE);
}

static inline void push_increase_dlevel(op_stack_t *stack) {
  push_op(stack, INCREASE_DLEVEL);
}

static inline void push_push(op_stack_t *stack) {
  push_op(stack, PUSH);
}



/*
 * Test bench
 */
typedef struct test_bench_s {
  uint32_t base_level;
  uint32_t decision_level;
  bool conflict;        // true if a contradiction is found (in test_assert_eq)
  int32_t conflict_eq;  // id of the first conflict equality
  bool mngr_conflict;   // true if offset_manager_propagates returns a conflict
  bool show_details;    // true for showing more stuff during testing

  poly_table_t *ptable;
  substitution_t subst;
  subst_queue_t squeue;
  active_poly_table_t act;
  op_stack_t stack;
  equality_queue_t equeue;
  offset_manager_t manager; // under test

  poly_buffer_t buffer; // for normalization
} test_bench_t;

static void init_test_bench(test_bench_t *bench, poly_table_t *ptable) {
  uint32_t nv, np;

  np = ptable->npolys;
  nv = ptable->nvars;

  bench->base_level = 0;
  bench->decision_level = 0;
  bench->conflict = false;
  bench->conflict_eq = -1;
  bench->mngr_conflict = false;
  bench->show_details = false;

  bench->ptable = ptable;
  init_substitution(&bench->subst, np);
  init_subst_queue(&bench->squeue, nv);
  init_active_polys(&bench->act, np);
  init_op_stack(&bench->stack);
  init_equality_queue(&bench->equeue, np);

  init_offset_manager(&bench->manager, &bench->equeue, notify_equality);

  init_poly_buffer(&bench->buffer);
}

static void delete_test_bench(test_bench_t *bench) {
  delete_substitution(&bench->subst);
  delete_subst_queue(&bench->squeue);
  delete_active_polys(&bench->act);
  delete_equality_queue(&bench->equeue);
  delete_op_stack(&bench->stack);
  delete_offset_manager(&bench->manager);
  delete_poly_buffer(&bench->buffer);
}


/*
 * Undo substitution:
 * - remove all substitutions until the mark in squeue
 * - if there's no mark, then remove all substitutions
 */
static void test_bench_undo_subst(test_bench_t *bench) {
  subst_queue_t *queue;
  uint32_t i;
  int32_t x;

  queue = &bench->squeue;
  i = queue->top;
  while (i > 0) {
    i --;
    x = queue->data[i];
    if (x < 0) break;
    remove_subst(&bench->subst, x);
  }
  queue->top = i;
}


/*
 * Undo acivations
 * - remove all active polynomials and pop the op stack
 *   until the top-most PUSH operation
 */
static void test_bench_undo_activations(test_bench_t *bench) {
  op_stack_t *stack;
  uint32_t i;

  stack = &bench->stack;

  i = stack->top;
  for (;;) {
    assert(i > 0);
    i --;
    switch (stack->data[i].tag) {
    case RECORD_POLY:
      remove_active_poly(&bench->act);
      break;

    case ASSERT_EQ:
    case PROPAGATE:
    case INCREASE_DLEVEL:
      break;

    case PUSH:
      goto done;
    }
  }

 done:
  stack->top = i;

  if (bench->conflict) {
    // check whether the conflict equality has been removed
    assert(bench->conflict_eq >= 0);
    if (i <= bench->conflict_eq) {
      bench->conflict_eq = -1;
      bench->conflict = false;
      bench->mngr_conflict = false;
      printf("---> Conflict resolved\n");
      fflush(stdout);
    }
  }

}


/*
 * Undo assert_var/keep record poly
 * - stop on the top-most 'INCREASE_DLEVEL'
 */
static void op_stack_backtrack(test_bench_t *bench) {
  op_stack_t *stack;
  ivector_t saved_polys;
  uint32_t i;
  int32_t id;

  stack = &bench->stack;

  init_ivector(&saved_polys, 10);
  i = stack->top;
  for (;;) {
    assert(i > 0);
    i --;
    switch (stack->data[i].tag) {
    case RECORD_POLY:
      id = stack->data[i].arg.rec_id;
      ivector_push(&saved_polys, id);
      break;

    case ASSERT_EQ: // undo
    case PROPAGATE: // undo
      break;

    case INCREASE_DLEVEL:
      goto done;

    case PUSH:
    default:
      assert(false);
      break;
    }
  }

 done:
  stack->top = i;

  if (bench->conflict) {
    // check whether the conflict equality has been removed
    assert(bench->conflict_eq >= 0);
    if (i <= bench->conflict_eq) {
      bench->conflict_eq = -1;
      bench->conflict = false;
      bench->mngr_conflict = false;
      printf("---> Conflict resolved\n");
      fflush(stdout);
    }
  }


  // redo the record poly operations
  i = saved_polys.size;
  while (i > 0) {
    i --;
    id = saved_polys.data[i];
    push_record_poly(stack, id);
  }

  delete_ivector(&saved_polys);
}


/*
 * Compute normal form of active poly k
 */
static void normalize(test_bench_t *bench, uint32_t k) {
  poly_buffer_t *buffer;
  int32_t idx;

  assert(0 <= k && k < bench->act.npolys);
  buffer = &bench->buffer;
  idx = bench->act.id[k];

  subst_poly_idx(&bench->subst, bench->ptable, buffer, idx);
  set_normal_form(bench->act.norm[k], buffer);
}

static void normalize_all(test_bench_t *bench) {
  uint32_t i, n;

  n = bench->act.npolys;
  for (i=0; i<n; i++) {
    normalize(bench, i);
  }
}


/*
 * Expected classes (based on normal forms)
 * - this collects all equal polynomials (must be called after normalize_all)
 */

// hash code (callback for int_partition: aux is a bench, i is the index of an active poly)
static uint32_t exp_hash_var(void *aux, int32_t i) {
  test_bench_t *bench;

  bench = aux;
  assert(0 <= i && i < bench->act.npolys);
  return bench->act.norm[i]->hash;
}

// equivalence tst
static bool exp_equal_var(void *aux, int32_t i, int32_t j) {
  test_bench_t *bench;

  bench = aux;
  assert(0 <= i && i < bench->act.npolys);
  assert(0 <= j && j < bench->act.npolys);
  return equal_normal_forms(bench->act.norm[i], bench->act.norm[j]);
}


static void collect_expected_classes(test_bench_t *bench, ipart_t *partition) {
  uint32_t i, n;

  n = bench->act.npolys;
  for (i=0; i<n; i++) {
    int_partition_add(partition, i);
  }
}



/*
 * Build a substitution from the equalities stored in v
 * - every element of v must be the id of a asserted equality
 * - if an equality can't be added to the substitution, it's left in v
 */
static substitution_t *subst_from_explanation(test_bench_t *bench, ivector_t *v) {
  substitution_t *s;
  op_stack_t *stack;
  offset_equality_t e;
  uint32_t i, j, n;
  int32_t id;

  s = (substitution_t *) safe_malloc(sizeof(substitution_t));
  init_substitution(s, bench->ptable->npolys);

  stack = &bench->stack;

  j = 0;
  n = v->size;
  for (i=0; i<n; i++) {
    id = v->data[i];
    assert(0 <= id && id < stack->top);
    assert(stack->data[id].tag == ASSERT_EQ);

    e = stack->data[id].arg.eq; // make a copy of eq[id]
    subst_eq(s, &e);           // normalize eq modulo previous equalities
    if (e.lhs == e.rhs) {
      // keep in v
      v->data[j] = id;
      j ++;
    } else {
      // add to subst
      if (e.lhs < 0) {  // convert 0 := rhs + offset into rhs = - offset
	e.lhs = e.rhs;
	e.rhs = -1;
	e.offset = - e.offset;
      }
      add_subst(s, e.lhs, e.rhs, e.offset);
    }
  }

  v->size = j;

  return s;
}


// delete substitution built by the previous function
static void free_substitution(substitution_t *s) {
  delete_substitution(s);
  safe_free(s);
}



/*
 * PRINT FUNCTIONS
 */
static void print_mono(const char *prefix, rational_t *coeff, int32_t x, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      printf("- ");
    } else {
      printf(" - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      printf(" + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (x == const_idx) {
    q_print_abs(stdout, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(stdout, coeff);
      printf(" * ");
    }
    printf("%s%"PRId32, prefix, x);
  }
}

static void print_poly(polynomial_t *p) {
  uint32_t i, n;
  bool first;

  if (polynomial_is_zero(p)) {
    printf("0");
  } else {
    n = p->nterms;
    first = true;
    for (i=0; i<n; i++) {
      print_mono("x", &p->mono[i].coeff, p->mono[i].var, first);
      first = false;
    }
  }
}

static void print_buffer(poly_buffer_t *b) {
  monomial_t *mono;
  uint32_t i, n;
  bool first;

  n = poly_buffer_nterms(b);
  mono = poly_buffer_mono(b);
  if (n == 0) {
    printf("0");
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_mono("x", &mono[i].coeff, mono[i].var, first);
      first = false;
    }
  }
}


static void print_normal_form(normal_form_t *f) {
  uint32_t i, n;
  bool first;

  n = f->nterms;
  if (n == 0) {
    printf("0");
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_mono("x", &f->mono[i].coeff, f->mono[i].var, first);
      first = false;
    }
  }
}

static void print_poly_table(poly_table_t *table) {
  polynomial_t *p;
  uint32_t i, n;

  n = table->npolys;
  for (i=0; i<n; i++) {
    p = table->poly[i];
    if (p != NULL) {
      printf("  x%"PRIu32" := ", i);
      print_poly(p);
      printf("\n");
    }
  }
}

static void print_poly_def(poly_table_t *table, int32_t id) {
  polynomial_t *p;

  assert(0 <= id && id < table->npolys);

  p = table->poly[id];
  if (p != NULL) {
    printf("    x%"PRId32" := ", id);
    print_poly(p);
    printf("\n");
  }
}

static void print_active_polys(test_bench_t *bench) {
  polynomial_t *p;
  uint32_t i, n;
  int32_t idx;

  n = bench->act.npolys;
  for (i=0; i<n; i++) {
    idx = bench->act.id[i];
    printf("  act[%"PRIu32"]: x%"PRId32, i, idx);
    p = bench->ptable->poly[idx];
    if (p != NULL) {
      printf(" = ");
      print_poly(p);
    }
    printf("\n");
  }
  printf("\n");
}


static void print_normal_forms(test_bench_t *bench) {
  uint32_t i, n;
  int32_t idx;

  n = bench->act.npolys;
  for (i=0; i<n; i++) {
    idx = bench->act.id[i];
    printf("  norm(x%"PRId32") = ", idx);
    print_normal_form(bench->act.norm[i]);
    printf("\n");
  }
  printf("\n");
}

static void print_offset_eq(offset_equality_t *eq) {
  if (eq->lhs < 0) {
    printf("0");
  } else {
    printf("x%"PRId32, eq->lhs);
  }
  printf(" == ");
  if (eq->rhs < 0) {
    printf("%"PRId32, eq->offset);
  } else {
    printf("x%"PRId32, eq->rhs);
    if (eq->offset > 0) {
      printf(" + %"PRId32, eq->offset);
    } else if (eq->offset < 0) {
      printf(" - %"PRId32, -eq->offset);
    }
  }
}

static void print_all_equalities(test_bench_t *bench) {
  uint32_t i, n;

  n = bench->stack.top;
  for (i=0; i<n; i++) {
    if (bench->stack.data[i].tag == ASSERT_EQ) {
      printf("  eq[%"PRIu32"]: ", i);
      print_offset_eq(&bench->stack.data[i].arg.eq);
      printf("\n");
    }
  }
  printf("\n");
}

static void print_class(int32_t *v) {
  uint32_t i, n;

  n = iv_size(v);
  assert(n >= 2);
  printf("{ x%"PRId32, v[0]);
  for (i=1; i<n; i++) {
    printf(", x%"PRId32, v[i]);
  }
  printf(" }");
}

static void print_infered_classes(test_bench_t *bench) {
  ipart_t partition;
  int32_t *v;
  uint32_t i, n;

  init_int_partition(&partition, 0, &bench->equeue, prop_hash_var, prop_same_class);
  collect_propagated_classes(&bench->equeue, &partition);

  n = int_partition_nclasses(&partition);
  for (i=0; i<n; i++) {
    v = partition.classes[i];
    printf("  class[%"PRIu32"]: ", i);
    print_class(v);
    printf("\n");
  }
  printf("\n");

  delete_int_partition(&partition);
}

static void print_active_class(active_poly_table_t *table, int32_t *v) {
  uint32_t i, n, k;

  n = iv_size(v);
  assert(n >= 2);

  k = v[0];
  assert(0 <= k && k < table->npolys);
  printf("{ x%"PRId32, table->id[k]);
  for (i=1; i<n; i++) {
    k = v[i];
    assert(0 <= k && k < table->npolys);
    printf(", x%"PRId32, table->id[k]);
  }
  printf(" }");
}

static void print_expected_classes(test_bench_t *bench) {
  ipart_t partition;
  int32_t *v;
  uint32_t i, n;

  init_int_partition(&partition, 0, bench, exp_hash_var, exp_equal_var);
  collect_expected_classes(bench, &partition);

  n = int_partition_nclasses(&partition);
  for (i=0; i<n; i++) {
    v = partition.classes[i];
    printf("  check[%"PRIu32"]: ", i);
    print_active_class(&bench->act, v);;
    printf("\n");
  }
  printf("\n");

  delete_int_partition(&partition);
}

static void print_explanation(test_bench_t *bench, ivector_t *v) {
  uint32_t i, n;
  int32_t id;

  n = v->size;
  for (i=0; i<n; i++) {
    id = v->data[i];
    assert(bench->stack.data[id].tag == ASSERT_EQ);
    printf("    eq[%"PRId32"]: ", id);
    print_offset_eq(&bench->stack.data[id].arg.eq);
    printf("\n");
  }
  printf("\n");
}


/*
 * Get the conflict explanation from bench->manager
 */
static void check_conflict(test_bench_t *bench, ivector_t *expl) {
  substitution_t *subst;
  op_stack_t *stack;
  offset_equality_t e;
  int32_t id;

  stack = &bench->stack;
  subst = subst_from_explanation(bench, expl);
  if (expl->size == 1) {
    id = expl->data[0];
    assert(0 <= id && id < stack->top);
    assert(stack->data[id].tag == ASSERT_EQ);

    e = stack->data[id].arg.eq;
    subst_eq(subst, &e);
    if (e.lhs == e.rhs && e.offset != 0) {
      printf("Conflict explanation looks correct\n");
    } else {
      printf("BUG: invalid conflict explanation\n");
      fflush(stdout);
      exit(1);
    }
  } else {
    printf("BUG: too many equaliteis in conflict eplanation\n");
    fflush(stdout);
    exit(1);
  }

  free_substitution(subst);
}


static bool equal_poly_buffers(poly_buffer_t *bx, poly_buffer_t *by) {
  return poly_buffer_nterms(bx) == poly_buffer_nterms(by) &&
    equal_monarrays(poly_buffer_mono(bx), poly_buffer_mono(by));
}

static void check_equality(test_bench_t *bench, int32_t x, int32_t y, ivector_t *expl) {
  substitution_t *subst;
  poly_buffer_t bx;
  poly_buffer_t by;

  assert(0 <= x && x < bench->ptable->npolys &&
	 0 <= y && y < bench->ptable->npolys &&
	 x != y);

  subst = subst_from_explanation(bench, expl);
  if (expl->size > 0) {
    printf("BUG: invalid explanation\n");
    fflush(stdout);
    exit(1);
  }

  // apply subst to x: result in bx
  init_poly_buffer(&bx);
  subst_poly_idx(subst, bench->ptable, &bx, x);

  // subst to y: result in by
  init_poly_buffer(&by);
  subst_poly_idx(subst, bench->ptable, &by, y);

  // check that the normal forms are the same
  if (! equal_poly_buffers(&bx, &by)) {
    printf("Explanation for x%"PRId32" == x%"PRId32":\n", x, y);
    print_poly_def(bench->ptable, x);
    print_poly_def(bench->ptable, y);
    print_explanation(bench, expl);
    printf("BUG: explantion does not imply x%"PRId32" == x%"PRId32"\n", x, y);
    printf("  subst for x%"PRId32" --> ", x);
    print_buffer(&bx);
    printf("\n");
    printf("  subst for x%"PRId32" --> ", y);
    print_buffer(&by);
    printf("\n");

    fflush(stdout);
    exit(1);
  }

  delete_poly_buffer(&bx);
  delete_poly_buffer(&by);
  free_substitution(subst);
}

static void check_propagation(test_bench_t *bench) {
  equality_queue_t *queue;
  ivector_t expl;
  uint32_t i, n;
  int32_t x, y;

  init_ivector(&expl, 10);

  queue = &bench->equeue;
  n = queue->top;
  for (i=0; i<n; i++) {
    x = queue->data[i].lhs;
    y = queue->data[i].rhs;
    if (x >= 0) {
      assert(y >= 0);

      offset_manager_explain_equality(&bench->manager, x, y, &expl);
      check_equality(bench, x, y, &expl);
      if (bench->show_details) {
	printf("Explanation for x%"PRId32" == x%"PRId32":\n", x, y);
	print_poly_def(bench->ptable, x);
	print_poly_def(bench->ptable, y);
	print_explanation(bench, &expl);
      }

      ivector_reset(&expl);
    }
  }

  delete_ivector(&expl);
}

// all elements of v should be in the same class: check wether that's true
// in the equality queue
static void check_good_class(test_bench_t *bench, int32_t *v) {
  active_poly_table_t *table;
  equality_queue_t *queue;
  polynomial_t *p;
  uint32_t i, n;
  int32_t k, x, y;

  queue = &bench->equeue;
  table = &bench->act;

  n = iv_size(v);
  assert(n >= 2);
  k = v[0];
  assert(0 <= k && k < table->npolys);
  x = table->id[k];

  for (i=1; i<n; i++) {
    k = v[i];
    assert(0 <= k && k < table->npolys);
    y = table->id[k];

    if (root_of_var(queue, x) != root_of_var(queue, y)) {
      printf("BUG: MISSED Propagation: x%"PRId32" and x%"PRId32" should be equal\n\n", x, y);
      printf("  act[%"PRId32"]: x%"PRId32, v[0], x);
      p = bench->ptable->poly[x];
      if (p != NULL) {
	printf(" = ");
	print_poly(p);
      }
      printf("\n");
      printf("  act[%"PRId32"]: x%"PRId32, k, y);
      p = bench->ptable->poly[y];
      if (p != NULL) {
	printf(" = ");
	print_poly(p);
      }
      printf("\n\n");
      print_all_equalities(bench);
      printf("  norm(x%"PRId32") = ", x);
      print_normal_form(bench->act.norm[v[0]]);
      printf("\n");
      printf("  norm(x%"PRId32") = ", y);
      print_normal_form(bench->act.norm[k]);
      printf("\n\n");
      fflush(stdout);
      exit(1);
    }
  }
}

static void check_all_propagated(test_bench_t *bench) {
  ipart_t partition;
  int32_t *v;
  uint32_t i, n;

  init_int_partition(&partition, 0, bench, exp_hash_var, exp_equal_var);
  collect_expected_classes(bench, &partition);

  n = int_partition_nclasses(&partition);
  for (i=0; i<n; i++) {
    v = partition.classes[i];
    check_good_class(bench, v);
  }

  delete_int_partition(&partition);
}



/*
 * TEST OPERATIONS
 */
static void test_activate(test_bench_t *bench, int32_t id) {
  polynomial_t *p;

  printf("[%"PRIu32"]: TEST_ACTIVATE: x%"PRId32"\n", ctr, id);

  add_active_poly(&bench->act, bench->ptable, id);
  push_record_poly(&bench->stack, id);

  p = bench->ptable->poly[id];
  record_offset_poly(&bench->manager, id, id, p);

  ctr ++;
}

static void test_assert_eq(test_bench_t *bench, int32_t x, int32_t y, int32_t offset) {
  offset_equality_t e;
  rational_t q;
  int32_t id;

  id = push_assert_eq(&bench->stack, x, y, offset);

  e.lhs = x;
  e.rhs = y;
  e.offset = offset;

  printf("[%"PRIu32"]: TEST_ASSERT_EQ: eq[%"PRId32"]: ", ctr, id);
  print_offset_eq(&e);
  printf("\n");

  subst_eq(&bench->subst, &e);

  // if e.lhs == e.rhs, we can't add to the substitution table
  if (e.lhs != e.rhs) {
    if (e.lhs < 0) {
      // convert 0 = y + offset into y := -offset
      e.lhs = e.rhs;
      e.rhs = -1;
      e.offset = -e.offset;
    }
    // add substitution e.lhs := e.rhs + e.offset
    add_subst(&bench->subst, e.lhs, e.rhs, e.offset);
    subst_queue_push_var(&bench->squeue, e.lhs);
  } else if (e.offset != 0) {
    bench->conflict = true;
    printf("---> Conflict\n");
    fflush(stdout);
    if (bench->conflict_eq < 0) {
      bench->conflict_eq = id;
    }
  }

  // forward to the offset manager
  q_init(&q);
  q_set32(&q, offset);
  assert_offset_equality(&bench->manager, x, y, &q, id);
  q_clear(&q);

  ctr ++;
}

static void test_propagate(test_bench_t *bench) {
  ivector_t expl;

  printf("[%"PRIu32"]: TEST_PROPAGATE: decision level = %"PRIu32", base level = %"PRIu32"\n", ctr, bench->decision_level, bench->base_level);
  push_propagate(&bench->stack);
  normalize_all(bench);

  if (bench->show_details) {
    printf("Active polys\n");
    print_active_polys(bench);
    printf("Assertions\n");
    print_all_equalities(bench);
    printf("Normal forms\n");
    print_normal_forms(bench);
  }

  if (bench->conflict) {
    printf("Expected result: conflict\n\n");
  } else {
    printf("Expected classes\n");
    print_expected_classes(bench);
  }

  if (offset_manager_propagate(&bench->manager)) {
    bench->mngr_conflict = false;
    printf("Propagated classes\n");
    print_infered_classes(bench);
    check_propagation(bench);
    check_all_propagated(bench);
    if (bench->conflict) {
      printf("BUG: conflict expected\n");
      fflush(stdout);
      exit(1);
    }

  } else {
    bench->mngr_conflict = true;
    printf("Conflict\n");
    init_ivector(&expl, 10);
    offset_manager_explain_conflict(&bench->manager, &expl);
    print_explanation(bench, &expl);
    check_conflict(bench, &expl);
    delete_ivector(&expl);

    if (! bench->conflict) {
      printf("BUG: conflict unexpected\n");
      fflush(stdout);
      exit(1);
    }
  }

  ctr ++;
}

static void test_push(test_bench_t *bench) {
  assert(bench->decision_level == bench->base_level);

  printf("[%"PRIu32"]: TEST_PUSH to base level %"PRIu32"\n", ctr, bench->base_level + 1);
  push_push(&bench->stack);
  push_mark(&bench->equeue);
  subst_queue_push_mark(&bench->squeue);
  bench->base_level ++;
  bench->decision_level ++;
  offset_manager_push(&bench->manager);

  ctr ++;
}

static void test_increase_dlevel(test_bench_t *bench) {
  printf("[%"PRIu32"]: INCREASE DECISION LEVEL to decision level %"PRIu32"\n", ctr, bench->decision_level + 1);
  push_increase_dlevel(&bench->stack);
  push_mark(&bench->equeue);
  subst_queue_push_mark(&bench->squeue);
  bench->decision_level ++;
  offset_manager_increase_decision_level(&bench->manager);

  ctr ++;
}


// bactkrack one level
static void test_backtrack(test_bench_t *bench) {
  assert(bench->decision_level > bench->base_level);

  printf("[%"PRIu32"]: TEST BACKTRACK to decision level %"PRIu32"\n", ctr, bench->decision_level - 1);
  equality_queue_backtrack(&bench->equeue);
  test_bench_undo_subst(bench);
  op_stack_backtrack(bench);
  bench->decision_level --;


  if (bench->show_details) {
    // print state after backtracking
    printf("AFTER BACKTRACK: decision level = %"PRIu32", base level = %"PRIu32"\n", bench->decision_level, bench->base_level);
    normalize_all(bench);
    printf("Active polys\n");
    print_active_polys(bench);
    printf("Assertions\n");
    print_all_equalities(bench);
    printf("Normal forms\n");
    print_normal_forms(bench);
  }

  offset_manager_backtrack(&bench->manager, bench->decision_level);

  ctr ++;
}


static void test_pop(test_bench_t *bench) {
  assert(bench->base_level > 0);

  printf("[%"PRIu32"]: TEST POP to base level %"PRIu32"\n", ctr, bench->base_level - 1);

  if (bench->decision_level > bench->base_level) {
    // backtrack in the test_bench
    do {
      equality_queue_backtrack(&bench->equeue);
      test_bench_undo_subst(bench);
      op_stack_backtrack(bench);
      bench->decision_level --;
    } while (bench->decision_level > bench->base_level);

    // backtrack in offset_manager
    offset_manager_backtrack(&bench->manager, bench->decision_level);
  }

  // bactrack once more
  equality_queue_backtrack(&bench->equeue);
  test_bench_undo_subst(bench);
  test_bench_undo_activations(bench);
  bench->decision_level --;
  bench->base_level --;

  if (bench->show_details) {
    // print state after pop
    printf("AFTER POP: decision level = %"PRIu32", base level = %"PRIu32"\n", bench->decision_level, bench->base_level);
    normalize_all(bench);
    printf("Active polys\n");
    print_active_polys(bench);
    printf("Assertions\n");
    print_all_equalities(bench);
    printf("Normal forms\n");
    print_normal_forms(bench);
  }

  offset_manager_pop(&bench->manager);

  ctr ++;
}



/*
 * Random tests
 */

// randomly pick an inactive polynomial in the act table
// return -1 if all polys are active
static int32_t random_inactive_poly(test_bench_t *bench) {
  active_poly_table_t *atbl;
  uint32_t n, k, max_iter;

  atbl = &bench->act;

  max_iter = 10;
  n = bench->ptable->npolys;
  k = random_index(n);

  while (atbl->active[k] && max_iter > 0) {
    max_iter --;
    k ++;
    if (k >= n) {
      k = 0;
    }
  }

  if (max_iter == 0) {
    return -1;
  } else {
    assert(!atbl->active[k]);
    return k;
  }
}


// attempt to activate n polynomials
static void random_activate(test_bench_t *bench, uint32_t n) {
  int32_t id;

  while (n > 0) {
    n --;
    id = random_inactive_poly(bench);
    if (id > 0) {
      test_activate(bench, id);
    }
  }
}



// pick a random active poly, then a random variable in this poly
// return -1 if p is constant
static int32_t var_of_poly(polynomial_t *p) {
  uint32_t i, n;
  int32_t x;

  n = p->nterms;
  if (n == 0 || (n == 1 && p->mono[0].var == const_idx)) {
    // p is constant
    x = -1;
  } else  {
    if (p->mono[0].var == const_idx) {
      assert(n >= 2);
      i = 1 + random_index(n - 1);
    } else {
      i = random_index(n);
    }
    x = p->mono[i].var;
    assert(x != const_idx);
  }

  return x;
}

static int32_t random_var_of_poly(test_bench_t *bench) {
  active_poly_table_t *atbl;
  polynomial_t *p;
  uint32_t i, n;
  int32_t id;

  atbl = &bench->act;
  n = atbl->npolys;
  id = -1; // in case n is 0
  if (n > 0) {
    i = random_index(n);
    id = atbl->id[i];
    assert(0 < id && id < bench->ptable->npolys);
    p = bench->ptable->poly[id];
    // if p is NULL, then it represents the variable id
    // so we just return id. Otherwise, we pick a variable of p
    if (p != NULL) {
      id = var_of_poly(p);
    }
  }

  return id;
}

static void random_assert_eq(test_bench_t *bench) {
  int32_t x, y, k;

  x = random_var_of_poly(bench);
  y = random_var_of_poly(bench);
  k = random_constant();

  test_assert_eq(bench, x, y, k);
}




/*
 * Random test: give more weight to assert_eq and propagate
 * - if there's a conflict, try to resolve it first
 */
static void random_op(test_bench_t *bench) {
  uint32_t r;

  if (bench->mngr_conflict) {
    if (bench->decision_level > bench->base_level) {
      test_backtrack(bench);
    } else if (bench->base_level > 0) {
      test_pop(bench);
    }
  } else {
    r = random_index(15);
    switch (r) {
    case 0:
    case 1:
    case 2:
    case 3:
    case 4:
      random_assert_eq(bench);
      break;

    case 5:
      random_assert_eq(bench);
    case 6:
      random_assert_eq(bench);
    case 7:
      random_assert_eq(bench);
    case 8:
      test_propagate(bench);
      break;

    case 9:
      random_activate(bench, 1);
      break;

    case 10:
    case 11:
      // increase decision level: force propagate first
      test_propagate(bench);
      if (! bench->mngr_conflict) {
	test_increase_dlevel(bench);
      }
      break;

    case 12:
      // push
      if (bench->decision_level == bench->base_level) {
	test_push(bench);
      }
      break;

    case 13:
      // backtrack
      if (bench->decision_level > bench->base_level) {
	test_backtrack(bench);
      }
      break;

    case 14:
      // pop
      if (bench->base_level > 0) {
	test_pop(bench);
      }
      break;

    default:
      assert(false);
      break;
    }
  }
}




/*
 * GLOBAL OBJECTS
 */
static poly_table_t poly_table;
static test_bench_t bench;


/*
 * Some simple tests
 */
static void base_test(void) {
  printf("*****************\n");
  printf("    BASE TESTS\n");
  printf("*****************\n\n");

  init_test_bench(&bench, &poly_table);
  bench.show_details = true;

  test_activate(&bench, 10);
  test_activate(&bench, 2);
  test_activate(&bench, 4);
  test_propagate(&bench);
  test_push(&bench);
  test_activate(&bench, 24);
  test_activate(&bench, 23);
  test_activate(&bench, 41);
  test_activate(&bench, 49);
  test_activate(&bench, 55);
  test_propagate(&bench);
  test_assert_eq(&bench, 4, 2, -12);
  test_assert_eq(&bench, 4, 10, 0);
  test_propagate(&bench);
  test_increase_dlevel(&bench);
  test_assert_eq(&bench, 5, -1, 1223);
  test_propagate(&bench);
  test_assert_eq(&bench, 2, 10, 20); // cause a conflict
  test_propagate(&bench);
  test_backtrack(&bench);
  test_propagate(&bench);
  test_pop(&bench);
  test_propagate(&bench);
  delete_test_bench(&bench);
}


/*
 * Random test:
 * - p = number of polynomials to activate first
 * - n = number of random operations
 */
static void random_test(uint32_t n, uint32_t p) {
  printf("*******************\n");
  printf("    RANDOM TESTS\n");
  printf("*******************\n\n");

  init_test_bench(&bench, &poly_table);

  random_activate(&bench, p);
  while (n > 0) {
    random_op(&bench);
    n --;
  }

  // final step: propagate
  if (! bench.mngr_conflict) {
    test_propagate(&bench);
  }

  delete_test_bench(&bench);
}


int main(void) {
  uint32_t n;

  init_rationals();
  init_poly_table(&poly_table, 100, 20);
  build_poly_table(&poly_table, 100, 1000);

  printf("==== ALL POLYS ====\n");
  print_poly_table(&poly_table);
  printf("====\n");

  base_test();
  random_test(1000, 40);

  n = 1000;
  while (n > 0) {
    random_test(4000, 200);
    n --;
  }

  n = 1000;
  while (n > 0) {
    random_test(4000, 100);
    n --;
  }

  delete_poly_table(&poly_table);
  cleanup_rationals();

  return 0;
}
