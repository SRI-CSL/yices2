/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR CONVERTING BIT-VECTOR POLYNOMIALS
 * TO ELEMENTARY EXPRESSIONS.
 */

#include <assert.h>

#include "solvers/bv/bvpoly_compiler.h"
#include "terms/bv64_constants.h"
#include "utils/bit_tricks.h"


#define TRACE 0

#if TRACE

#include <stdio.h>
#include <inttypes.h>

#include "solvers/bv/bvsolver_printer.h"

#endif


/*
 * QUEUES
 */

/*
 * Initialize to empty queue
 */
static inline void init_bvc_queue(bvc_queue_t *queue) {
  queue->data = NULL;
  queue->top = 0;
  queue->size = 0;
}


/*
 * Make the queue larger
 */
static void bvc_queue_extend(bvc_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    // first allocation
    n = DEF_BVC_QUEUE_SIZE;
    assert(n > 0 && n <= MAX_BVC_QUEUE_SIZE && queue->data == NULL);
  } else {
    n += (n >> 1); // 50% large
    assert(n > queue->size);
    if (n > MAX_BVC_QUEUE_SIZE) {
      out_of_memory();
    }
  }

  queue->data = (thvar_t *) safe_realloc(queue->data, n * sizeof(thvar_t));
  queue->size = n;
}


/*
 * Push x on the queue
 */
static void bvc_queue_push(bvc_queue_t *queue, thvar_t x) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    bvc_queue_extend(queue);
  }
  assert(i < queue->size);
  queue->data[i] = x;
  queue->top = i + 1;
}


/*
 * Empty the queue
 */
static inline void reset_bvc_queue(bvc_queue_t *queue) {
  queue->top = 0;
}


/*
 * Delete
 */
static void delete_bvc_queue(bvc_queue_t *queue) {
  if (queue->data != NULL) {
    safe_free(queue->data);
    queue->data = NULL;
  }
}





/*
 * COMPILER
 */

/*
 * Initialize:
 * - vtbl = attached variable table
 * - mtbl = attached merge table
 */
void init_bv_compiler(bvc_t *c, bv_vartable_t *vtbl, mtbl_t *mtbl) {
  c->vtbl = vtbl;
  c->mtbl = mtbl;
  init_int_hmap(&c->cmap, 0);
  init_bvc_queue(&c->elemexp);

  init_bvc_dag(&c->dag, 0);
  init_bvc_queue(&c->queue);
  init_int_bvset(&c->in_queue, 0);

  init_ivector(&c->buffer, 10);
  init_bvpoly_buffer(&c->pbuffer);
  init_pp_buffer(&c->pp_buffer, 10);
}


/*
 * Delete
 */
void delete_bv_compiler(bvc_t *c) {
  delete_int_hmap(&c->cmap);
  delete_bvc_queue(&c->elemexp);

  delete_bvc_dag(&c->dag);
  delete_bvc_queue(&c->queue);
  delete_int_bvset(&c->in_queue);

  delete_ivector(&c->buffer);
  delete_bvpoly_buffer(&c->pbuffer);
  delete_pp_buffer(&c->pp_buffer);
}


/*
 * Empty
 */
void reset_bv_compiler(bvc_t *c) {
  int_hmap_reset(&c->cmap);
  reset_bvc_queue(&c->elemexp);

  reset_bvc_dag(&c->dag);
  reset_bvc_queue(&c->queue);
  reset_int_bvset(&c->in_queue);

  ivector_reset(&c->buffer);
  reset_bvpoly_buffer(&c->pbuffer, 32); // any bitsize would do
  pp_buffer_reset(&c->pp_buffer);
}



/*
 * For push/pop: remove all variables with index >= nv
 */
static bool record_to_remove(uint32_t *nv, int_hmap_pair_t *p) {
  return p->key >= *nv || p->val >= *nv;
}

static void bvc_queue_remove_vars(bvc_queue_t *q, uint32_t nv) {
  uint32_t i, n, j;
  thvar_t x;

  j = 0;
  n = q->top;
  for (i=0; i<n; i++) {
    x = q->data[i];
    if (x < nv) {
      q->data[j] = x;
      j ++;
    }
  }
  q->top = j;
}

void bv_compiler_remove_vars(bvc_t *c, uint32_t nv) {
  int_hmap_remove_records(&c->cmap, &nv, (int_hmap_filter_t) record_to_remove);
  bvc_queue_remove_vars(&c->elemexp, nv);
}



/*
 * Get the variable mapped to x in cmap
 * - return -1 if nothing is mapped to x
 */
thvar_t bvvar_compiles_to(bvc_t *c, thvar_t x) {
  int_hmap_pair_t *p;
  thvar_t y;

  assert(0 < x && x < c->vtbl->nvars);

  y = null_thvar;
  p = int_hmap_find(&c->cmap, x);
  if (p != NULL) {
    y = p->val;
    assert(0 < y && y < c->vtbl->nvars);
  }

  return y;
}


/*
 * Store the mapping [x --> y] in c->cmap
 */
static void bv_compiler_store_map(bvc_t *c, thvar_t x, thvar_t y) {
  int_hmap_pair_t *p;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars && x != y);

  p = int_hmap_get(&c->cmap, x);
  assert(p->val == -1);
  p->val = y;
}



/*
 * CONSTRUCTORS FOR ELEMENTARY EXPRESSIONS
 */

/*
 * Map x to a constant a
 * - n = number of bits in a
 */
static void bv_compiler_map_to_const64(bvc_t *c, thvar_t x, uint64_t a, uint32_t n) {
  thvar_t v;

  assert(1 <= n && n <= 64 && a == norm64(a, n));
  v = get_bvconst64(c->vtbl, n, a);
  bv_compiler_store_map(c, x, v);
}


static void bv_compiler_map_to_const(bvc_t *c, thvar_t x, uint32_t *a, uint32_t n) {
  thvar_t v;

  assert(n > 64 && bvconst_is_normalized(a, n));
  v = get_bvconst(c->vtbl, n, a);
  bv_compiler_store_map(c, x, v);
}


// variant: constant = 0
static void bv_compiler_map_to_zero(bvc_t *c, thvar_t x, uint32_t n) {
  uint32_t aux[8];
  uint32_t *a;
  uint32_t w;

  assert(n > 64);
  w = (n+31) >> 5;
  if (w <= 8) {
    bvconst_clear(aux, w);
    bv_compiler_map_to_const(c, x, aux, n);
  } else {
    a = bvconst_alloc(w);
    bvconst_clear(a, w);
    bv_compiler_map_to_const(c, x, a, n);
    bvconst_free(a, w);
  }
}


/*
 * In all constructors:
 * - n = number of bits
 * - x (and y) = operands
 */
static thvar_t bv_compiler_mk_bvadd(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;
  bool new;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);

  // normalize: left operand <= right operand
  if (x > y) {
    v = x; x = y; y = v;
  }

  v = get_bvadd(c->vtbl, n, x, y, &new);
  if (new) {
    bvc_queue_push(&c->elemexp, v);
  }

  return v;
}

static thvar_t bv_compiler_mk_bvsub(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;
  bool new;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);

  v = get_bvsub(c->vtbl, n, x, y, &new);
  if (new) {
    bvc_queue_push(&c->elemexp, v);
  }

  return v;
}

static thvar_t bv_compiler_mk_bvmul(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;
  bool new;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);

  // normalize: left operand <= right operand
  if (x > y) {
    v = x; x = y; y = v;
  }

  v = get_bvmul(c->vtbl, n, x, y, &new);
  if (new) {
    bvc_queue_push(&c->elemexp, v);
  }

  return v;
}

static thvar_t bv_compiler_mk_bvneg(bvc_t *c, uint32_t n, thvar_t x) {
  thvar_t v;
  bool new;

  assert(0 < x && x < c->vtbl->nvars);

  v = get_bvneg(c->vtbl, n, x, &new);
  if (new) {
    bvc_queue_push(&c->elemexp, v);
  }

  return v;
}

static thvar_t bv_compiler_mk_zero(bvc_t *c, uint32_t n) {
  uint32_t aux[8];
  uint32_t *a;
  uint32_t w;
  thvar_t v;

  assert(1 <= n);

  if (n <= 64) {
    v = get_bvconst64(c->vtbl, n, 0);
  } else {
    w = (n+31) >> 5;
    a = aux;
    if (w > 8) {
      a = bvconst_alloc(w);
    }
    bvconst_clear(aux, w);
    v = get_bvconst(c->vtbl, n, aux);
    if (w > 8) {
      bvconst_free(a, w);
    }
  }

  bvc_queue_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_const64(bvc_t *c, uint64_t a, uint32_t n) {
  thvar_t v;

  assert(1 <= n && n <= 64 && a == norm64(a, n));
  v = get_bvconst64(c->vtbl, n, a);
  bvc_queue_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_const(bvc_t *c, uint32_t *a, uint32_t n) {
  thvar_t v;

  assert(n > 64 && bvconst_is_normalized(a, n));
  v = get_bvconst(c->vtbl, n, a);
  bvc_queue_push(&c->elemexp, v);

  return v;
}


/*
 * POWER-PRODUCT CONSTRUCTION
 */

/*
 * Build (bvmul x y) but treat x = null_thvar as 1
 */
static thvar_t mk_bvmul_aux(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  return x == null_thvar ? y : bv_compiler_mk_bvmul(c, n, x, y);
}

/*
 * Build the variable x := (x_1^d_1 ... x_k^d_k)
 * - where x_1^d_1 ... x_k^d_k is stored in b
 * - n = number of bits in x_1 ... x_k
 * - the total degree d_1 + ... + d_k must be positive
 */
static thvar_t bv_compiler_mk_power_product(bvc_t *c, uint32_t n, pp_buffer_t *b) {
  varexp_t *a;
  ivector_t *v;
  uint32_t i,  m, d;
  bool zero_deg;
  thvar_t x;


  v = &c->buffer;
  ivector_reset(v);

  m = b->len;
  a = b->prod;

  do {
    zero_deg = true;
    x = null_thvar;
    /*
     * In each iteration:
     *  x = product of all variables x_i's that have odd degree
     *  (or null_thvar if all variables have even degree)
     *  d_i := d_i/2
     */
    for (i=0; i<m; i++) {
      d = a[i].exp;
      if ((d & 1) != 0) {
        x = mk_bvmul_aux(c, n, x, a[i].var);
      }
      d >>= 1;
      a[i].exp = d;
      zero_deg = zero_deg & (d == 0);
    }

    ivector_push(v, x);

  } while (! zero_deg);


  /*
   * v contains [x_0, ... x_t],
   * the result is x_0 * x_1^2 * x_2^4 ... * x_t^(2^t)
   */
  assert(v->size > 0);
  i = v->size - 1;
  x = v->data[i];
  assert(x != null_thvar);
  while (i > 0) {
    i --;
    x = bv_compiler_mk_bvmul(c, n, x, x);
    x = mk_bvmul_aux(c, n, v->data[i], x);
  }

  return x;
}



/*
 * SIMPLIFICATION
 */

/*
 * Apply the substitution stored in the merge table to p
 * - store the result in the poly_buffer b
 */
static void bv_compiler_simplify_poly64(bvc_t *c, bvpoly64_t *p,  bvpoly_buffer_t *b) {
  bv_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  reset_bvpoly_buffer(b, p->bitsize);

  vtbl = c->vtbl;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    bvpoly_buffer_add_const64(b, p->mono[0].coeff);
    i ++;
  }

  while (i < n) {
    assert(p->mono[i].var != const_idx);
    x = mtbl_get_root(c->mtbl, p->mono[i].var);
    //    x = bv_compiler_subst_var(c, p->mono[i].var);
    if (bvvar_is_const64(vtbl, x)) {
      bvpoly_buffer_add_const64(b, p->mono[i].coeff * bvvar_val64(vtbl, x));
    } else {
      bvpoly_buffer_add_mono64(b, x, p->mono[i].coeff);
    }
    i ++;
  }

  normalize_bvpoly_buffer(b);
}

static void bv_compiler_simplify_poly(bvc_t *c, bvpoly_t *p, bvpoly_buffer_t *b) {
  bv_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  reset_bvpoly_buffer(b, p->bitsize);

  vtbl = c->vtbl;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    bvpoly_buffer_add_constant(b, p->mono[0].coeff);
    i ++;
  }

  while (i < n) {
    assert(p->mono[i].var != const_idx);
    x = mtbl_get_root(c->mtbl, p->mono[i].var);
    //    x = bv_compiler_subst_var(c, p->mono[i].var);
    if (bvvar_is_const(vtbl, x)) {
      bvpoly_buffer_addmul_constant(b, p->mono[i].coeff, bvvar_val(vtbl, x));
    } else {
      bvpoly_buffer_add_monomial(b, x, p->mono[i].coeff);
    }
    i ++;
  }

  normalize_bvpoly_buffer(b);
}


/*
 * COMPILATION PHASE 1: STORE VARIABLES TO COMPILE
 */

/*
 * Check whether x is in cmap
 */
static inline bool bvvar_is_compiled(bvc_t *c, thvar_t x) {
  return int_hmap_find(&c->cmap, x) != NULL;
}


/*
 * Check whether x must be added to the queue
 * - i.e., x is not already compiled and not already in the queue
 */
static bool bvvar_to_process(bvc_t *c, thvar_t x) {
  return !int_bvset_member(&c->in_queue, x) && !bvvar_is_compiled(c, x);
}


/*
 * Add variable x to the internal queue
 * - also recursively add all the children of x
 *   so that the children precede x in c->queue
 */
static void bv_compiler_push_poly64(bvc_t *c, bvpoly64_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i = 1;
  }
  while (i < n) {
    x = mtbl_get_root(c->mtbl, p->mono[i].var);
    bv_compiler_push_var(c, x);
    i ++;
  }
}

static void bv_compiler_push_poly(bvc_t *c, bvpoly_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i = 1;
  }
  while (i < n) {
    x = mtbl_get_root(c->mtbl, p->mono[i].var);
    bv_compiler_push_var(c, x);
    i ++;
  }
}

static void bv_compiler_push_pprod(bvc_t *c, pprod_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->len;
  for (i=0; i<n; i++) {
    x = mtbl_get_root(c->mtbl, p->prod[i].var);
    bv_compiler_push_var(c, x);
  }
}


/*
 * Add x and all the variables on which x depends to the queue
 * - mark x first (to prevent looping if there are  circular dependencies)
 * - recursively push the children
 * - then add x to the queue
 */
void bv_compiler_push_var(bvc_t *c, thvar_t x) {
  bv_vartable_t *vtbl;

  assert(0 < x && x < c->vtbl->nvars);

  vtbl = c->vtbl;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_POLY64:
    if (bvvar_to_process(c, x)) {
      int_bvset_add(&c->in_queue, x);
      bv_compiler_push_poly64(c, bvvar_poly64_def(vtbl, x));
      bvc_queue_push(&c->queue, x);
    }
    break;

  case BVTAG_POLY:
    if (bvvar_to_process(c, x)) {
      int_bvset_add(&c->in_queue, x);
      bv_compiler_push_poly(c, bvvar_poly_def(vtbl, x));
      bvc_queue_push(&c->queue, x);
    }
    break;

  case BVTAG_PPROD:
    if (bvvar_to_process(c, x)) {
      int_bvset_add(&c->in_queue, x);
      bv_compiler_push_pprod(c, bvvar_pprod_def(vtbl, x));
      bvc_queue_push(&c->queue, x);
    }
    break;

  default:
    // skip x
    break;
  }
}



/*
 * COMPILATION PHASE 2: CONVERT TO THE DAG REPRESENTATION
 */

/*
 * Convert p to a DAG node
 * - return the node occurrence
 * - all variables of p that are not in dag->vsets are mapped to leaf nodes
 */
static node_occ_t bv_compiler_pprod_to_dag(bvc_t *c, pprod_t *p, uint32_t bitsize) {
  bvc_dag_t *dag;
  ivector_t *v;
  uint32_t i, n;
  thvar_t x;
  node_occ_t q;

  dag = &c->dag;

  v = &c->buffer;
  ivector_reset(v);

  n = p->len;
  for (i=0; i<n; i++) {
    x = mtbl_get_root(c->mtbl, p->prod[i].var);
    //    x = bv_compiler_subst_var(c, p->prod[i].var);
    q = bvc_dag_get_nocc_of_var(dag, x, bitsize);
    ivector_push(v, q);
  }

  return bvc_dag_pprod(dag, p, v->data, bitsize);
}


/*
 * Convert polynomial buffer b to DAG:
 * - b must not be constant
 */
static node_occ_t bv_compiler_pbuffer_to_dag(bvc_t *c, bvpoly_buffer_t *b) {
  bvc_dag_t *dag;
  ivector_t *v;
  uint32_t i, n, nbits;
  thvar_t x;
  node_occ_t q;

  assert(! bvpoly_buffer_is_constant(b));

  dag = &c->dag;

  v = &c->buffer;
  ivector_reset(v);

  n = bvpoly_buffer_num_terms(b);
  nbits = bvpoly_buffer_bitsize(b);

  i = 0;
  if (bvpoly_buffer_var(b, 0) == const_idx) {
    ivector_push(v, const_idx); // need a place-holder in v->data[0]
    i = 1;
  }
  while (i < n) {
    x = bvpoly_buffer_var(b, i);
    assert(x != const_idx && mtbl_is_root(c->mtbl, x));
    q = bvc_dag_get_nocc_of_var(dag, x, nbits);
    ivector_push(v, q);
    i++;
  }

  return bvc_dag_poly_buffer(dag, b, v->data);
}



/*
 * Build a DAG node for x and store the mapping [x --> node]
 * - x must be a polynomial or a power product
 */
static void bv_compiler_map_var_to_dag(bvc_t *c, thvar_t x) {
  bv_vartable_t *vtbl;
  bvpoly_buffer_t *b;
  node_occ_t q;
  uint64_t a;

  assert(0 < x && x < c->vtbl->nvars && int_bvset_member(&c->in_queue, x));

  q = -1; // Stop GCC warning

  vtbl = c->vtbl;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_POLY64:
    b = &c->pbuffer;
    bv_compiler_simplify_poly64(c, bvvar_poly64_def(vtbl, x), b);
    if (bvpoly_buffer_is_constant(b)) {
      a = 0;
      if (!bvpoly_buffer_is_zero(b)) {
        a = bvpoly_buffer_coeff64(b, 0);
      }
      bv_compiler_map_to_const64(c, x, a, b->bitsize);
      return;
    }
    q = bv_compiler_pbuffer_to_dag(c, b);
    break;

  case BVTAG_POLY:
    b = &c->pbuffer;
    bv_compiler_simplify_poly(c, bvvar_poly_def(vtbl, x), b);
    if (bvpoly_buffer_is_constant(b)) {
      if (bvpoly_buffer_is_zero(b)) {
        bv_compiler_map_to_zero(c, x, b->bitsize);
      } else {
        bv_compiler_map_to_const(c, x, bvpoly_buffer_coeff(b, 0), b->bitsize);
      }
      return;
    }
    q = bv_compiler_pbuffer_to_dag(c, b);
    break;

  case BVTAG_PPROD:
    q = bv_compiler_pprod_to_dag(c, bvvar_pprod_def(vtbl, x), bvvar_bitsize(vtbl, x));
    break;

  default:
    assert(false);
    break;
  }

  bvc_dag_map_var(&c->dag, x, q);
  int_bvset_remove(&c->in_queue, x);
}



/*
 * Simplify the DAG nodes using elementary expression x
 */

// case 1: x is (bvadd y z) where y != z and both y and z occur in the dag
static void bv_compiler_simplify_dag_bvadd(bvc_t *c, thvar_t x, thvar_t y, thvar_t z) {
  bvc_dag_t *dag;
  node_occ_t ny, nz, nx;
  uint32_t nbits;

  dag = &c->dag;
  ny = bvc_dag_nocc_of_var(dag, y);
  nz = bvc_dag_nocc_of_var(dag, z);
  if (bvc_dag_check_reduce_sum(dag, ny, nz)) {
    nbits = bvvar_bitsize(c->vtbl, x);
    assert(bvvar_bitsize(c->vtbl, y) == nbits &&
           bvvar_bitsize(c->vtbl, z) == nbits);

    nx = bvc_dag_leaf(dag, x, nbits);
    bvc_dag_reduce_sum(dag, nx, ny, nz);
  }
}

// case 2: x is (bvsub y z) where y != z and both y and z occur in the dag
static void bv_compiler_simplify_dag_bvsub(bvc_t *c, thvar_t x, thvar_t y, thvar_t z) {
  bvc_dag_t *dag;
  node_occ_t ny, nz, nx;
  uint32_t nbits;

  dag = &c->dag;
  ny = bvc_dag_nocc_of_var(dag, y);
  nz = negate_occ(bvc_dag_nocc_of_var(dag, z));
  if (bvc_dag_check_reduce_sum(dag, ny, nz)) {
    nbits = bvvar_bitsize(c->vtbl, x);
    assert(bvvar_bitsize(c->vtbl, y) == nbits &&
           bvvar_bitsize(c->vtbl, z) == nbits);

    nx = bvc_dag_leaf(dag, x, nbits);
    bvc_dag_reduce_sum(dag, nx, ny, nz);
  }
}

// case 3: x is (bvmul y z) where y and z occur in the dag
static void bv_compiler_simplify_dag_bvmul(bvc_t *c, thvar_t x, thvar_t y, thvar_t z) {
  bvc_dag_t *dag;
  node_occ_t ny, nz, nx;
  uint32_t nbits;

  dag = &c->dag;
  ny = bvc_dag_nocc_of_var(dag, y);
  nz = bvc_dag_nocc_of_var(dag, z);
  if (bvc_dag_check_reduce_prod(dag, ny, nz)) {
    nbits = bvvar_bitsize(c->vtbl, x);
    assert(bvvar_bitsize(c->vtbl, y) == nbits &&
           bvvar_bitsize(c->vtbl, z) == nbits);

    nx = bvc_dag_leaf(dag, x, nbits);
    bvc_dag_reduce_prod(dag, nx, ny, nz);
  }
}



static void bv_compiler_simplify_dag(bvc_t *c, thvar_t x) {
  bv_vartable_t *vtbl;
  bvc_dag_t *dag;
  thvar_t *aux;
  thvar_t y, z;

  dag = &c->dag;
  vtbl = c->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_ADD:
    aux = bvvar_binop(vtbl, x);
    y = mtbl_get_root(c->mtbl, aux[0]);
    z = mtbl_get_root(c->mtbl, aux[1]);
    if (y != z && bvc_dag_var_is_present(dag, y) && bvc_dag_var_is_present(dag, z)) {
      bv_compiler_simplify_dag_bvadd(c, x, y, z);
    }
    break;

  case BVTAG_SUB:
    aux = bvvar_binop(vtbl, x);
    y = mtbl_get_root(c->mtbl, aux[0]);
    z = mtbl_get_root(c->mtbl, aux[1]);
    if (y != z && bvc_dag_var_is_present(dag, y) && bvc_dag_var_is_present(dag, z)) {
      bv_compiler_simplify_dag_bvsub(c, x, y, z);
    }
    break;

  case BVTAG_MUL:
    aux = bvvar_binop(vtbl, x);
    y = mtbl_get_root(c->mtbl, aux[0]);
    z = mtbl_get_root(c->mtbl, aux[1]);
    if (bvc_dag_var_is_present(dag, y) && bvc_dag_var_is_present(dag, z)) {
      bv_compiler_simplify_dag_bvmul(c, x, y, z);
    }
    break;

  default:
    break;
  }
}



/*
 * PHASE 3: CONVERT NODES TO ELEMENTARY EXPRESSIONS
 */

/*
 * Compilation of an elementary node i
 */
// case 1: i is [offset a0 n]
static void bvc_process_offset(bvc_t *c, bvnode_t i, bvc_offset_t *d) {
  bv_vartable_t *vtbl;
  uint32_t nbits;
  thvar_t x, y, z;

  vtbl = c->vtbl;
  nbits = d->header.bitsize;
  if (nbits <= 64) {
    y = get_bvconst64(vtbl, nbits, d->constant.c);
  } else {
    y = get_bvconst(vtbl, nbits, d->constant.w);
  }
  z = bvc_dag_get_var_of_leaf(&c->dag, d->nocc);

  if (sign_of_occ(d->nocc) == 0) {
    // i is compiled to [bvadd y z]
    x = bv_compiler_mk_bvadd(c, nbits, y, z);
  } else {
    // i is compiled to [bvsub y z];
    x = bv_compiler_mk_bvsub(c, nbits, y, z);
  }
  bvc_dag_convert_to_leaf(&c->dag, i, x);
}

// case 2: i is [mono a0 n]
static void bvc_process_monomial(bvc_t *c, bvnode_t i, bvc_mono_t *d) {
  bv_vartable_t *vtbl;
  uint32_t nbits;
  thvar_t x, y, z;

  vtbl = c->vtbl;
  nbits = d->header.bitsize;
  if (nbits <= 64) {
    y = get_bvconst64(vtbl, nbits, d->coeff.c);
  } else {
    y = get_bvconst(vtbl, nbits, d->coeff.w);
  }
  z = bvc_dag_get_var_of_leaf(&c->dag, d->nocc);

  // i is compiled to [bvmul y z]
  x = bv_compiler_mk_bvmul(c, nbits, y, z);
  bvc_dag_convert_to_leaf(&c->dag, i, x);
}

// case 3: i is [prod n1 n2] or [prod n1^2]
static void bvc_process_elem_prod(bvc_t *c, bvnode_t i, bvc_prod_t *d) {
  uint32_t nbits;
  node_occ_t nx, ny, nz;
  thvar_t x, y, z;

  assert((d->len == 1 && d->prod[0].exp == 2) ||
         (d->len == 2 && d->prod[0].exp == 1 && d->prod[1].exp == 1));

  nbits = d->header.bitsize;

  ny = d->prod[0].var;
  y = bvc_dag_get_var_of_leaf(&c->dag, ny);
  nz = ny;
  z = y;
  if (d->len == 2) {
    nz = d->prod[1].var;
    z = bvc_dag_get_var_of_leaf(&c->dag, nz);
  }

  // i is compiled to [bvmul y z]
  x = bv_compiler_mk_bvmul(c, nbits, y, z);
  bvc_dag_convert_to_leaf(&c->dag, i, x);

  // now replace (ny * nz) by nx everywhere
  nx = bvp(i);
  bvc_dag_reduce_prod(&c->dag, nx, ny, nz);
}

// case 4: i is [sum n1 n2]
static void bvc_process_elem_sum(bvc_t *c, bvnode_t i, bvc_sum_t *d) {
  uint32_t nbits;
  node_occ_t nx, ny, nz;
  thvar_t x, y, z;

  assert(d->len == 2);

  nbits = d->header.bitsize;
  ny = d->sum[0];
  nz = d->sum[1];
  y = bvc_dag_get_var_of_leaf(&c->dag, ny);
  z = bvc_dag_get_var_of_leaf(&c->dag, nz);

  if (sign_of_occ(ny) == 0) {
    if (sign_of_occ(nz) == 0) {
      // i is compiled to [bvadd y z]
      x = bv_compiler_mk_bvadd(c, nbits, y, z);
    } else {
      // i is compiled to [bvsub y z]
      x = bv_compiler_mk_bvsub(c, nbits, y, z);
    }
  } else {
    if (sign_of_occ(nz) == 0) {
      // i is compiled to [bvsub z y]
      x = bv_compiler_mk_bvsub(c, nbits, z, y);
    } else {
      // i is compiled to [bnveg [bvadd y z]]?
      x = bv_compiler_mk_bvadd(c, nbits, y, z);
      x = bv_compiler_mk_bvneg(c, nbits, x);
    }
  }

  // replace ny nz by nx everywhere
  bvc_dag_convert_to_leaf(&c->dag, i, x);
  nx = bvp(i);
  bvc_dag_reduce_sum(&c->dag, nx, ny, nz);
}

// case 5: i is zero
static void bvc_process_zero(bvc_t *c, bvnode_t i, bvc_zero_t *d) {
  uint32_t nbits;
  thvar_t x;

  nbits = d->header.bitsize;
  x = bv_compiler_mk_zero(c, nbits);
  bvc_dag_convert_to_leaf(&c->dag, i, x);
}


// case 6: i is a constant node
static void bvc_process_constant(bvc_t *c, bvnode_t i, bvc_constant_t *d) {
  uint32_t nbits;
  thvar_t x;

  nbits = d->header.bitsize;
  if (nbits <= 64) {
    x = bv_compiler_mk_const64(c, d->value.c, nbits);
  } else {
    x = bv_compiler_mk_const(c, d->value.w, nbits);
  }
  bvc_dag_convert_to_leaf(&c->dag, i, x);
}


static void bvc_process_elem_node(bvc_t *c, bvnode_t i) {
  bvc_dag_t *dag;

  dag = &c->dag;
  switch (bvc_dag_node_type(dag, i)) {
  case BVC_ZERO:
    bvc_process_zero(c, i, bvc_dag_node_zero(dag, i));
    break;

  case BVC_CONSTANT:
    bvc_process_constant(c, i, bvc_dag_node_constant(dag, i));
    break;

  case BVC_OFFSET:
    bvc_process_offset(c, i, bvc_dag_node_offset(dag, i));
    break;

  case BVC_MONO:
    bvc_process_monomial(c, i, bvc_dag_node_mono(dag, i));
    break;

  case BVC_PROD:
    bvc_process_elem_prod(c, i, bvc_dag_node_prod(dag, i));
    break;

  case BVC_SUM:
    bvc_process_elem_sum(c, i, bvc_dag_node_sum(dag, i));
    break;

  case BVC_LEAF:
  case BVC_ALIAS:
    assert(false);
    break;
  }
}



/*
 * SIMPLE NODES
 */

/*
 * Check whether product or sum p is simple:
 * - return true if all the nodes occurring in p are leaves
 *   and p contains at most one shared leaf
 * - we take the degree into account: if p contains product x^k
 *   with k>1 and x is shared then that's more than one shared occurrence
 */
static bool bvc_prod_is_simple(bvc_dag_t *dag, bvc_prod_t *p) {
  uint32_t i, n, n_shared;
  node_occ_t nx;

  n_shared = 0;
  n = p->len;
  for (i=0; i<n; i++) {
    nx = p->prod[i].var;
    if (!bvc_dag_occ_is_leaf(dag, nx)) {
      return false;
    }
    if (bvc_dag_occ_is_shared(dag, nx)) {
      //      n_shared ++;
      n_shared += p->prod[i].exp;
      if (n_shared > 1) return false;
    }
  }

  assert(n_shared <= 1);

  return true;
}

static bool bvc_sum_is_simple(bvc_dag_t *dag, bvc_sum_t *p) {
  uint32_t i, n, n_shared;
  node_occ_t nx;

  n_shared = 0;
  n = p->len;
  for (i=0; i<n; i++) {
    nx = p->sum[i];
    if (!bvc_dag_occ_is_leaf(dag, nx)) {
      return false;
    }
    if (bvc_dag_occ_is_shared(dag, nx)) {
      n_shared ++;
      if (n_shared > 1) return false;
    }
  }

  assert(n_shared <= 1);

  return true;
}


/*
 * Compilation of a simple/non-elementary node i
 */
static void bvc_process_simple_prod(bvc_t *c, bvnode_t i, bvc_prod_t *p) {
  pp_buffer_t *pp;
  uint32_t j, m, nbits;
  thvar_t x;

  assert(p->len >= 1);

  pp = &c->pp_buffer;
  pp_buffer_reset(pp);

  /*
   * p is [n1^d1 ... n_m^d_m]
   * find x_i := variable of leaf node n_i
   * then build x = [x1^d1 ... x_m^d_m]
   */
  nbits = p->header.bitsize;
  m = p->len;
  for (j=0; j<m; j++) {
    x = bvc_dag_get_var_of_leaf(&c->dag, p->prod[j].var);
    pp_buffer_push_varexp(pp, x, p->prod[j].exp);
  }

  x = bv_compiler_mk_power_product(c, nbits, pp);

  // replace i by [leaf x] in DAG
  bvc_dag_convert_to_leaf(&c->dag, i, x);
}

static void bvc_process_simple_sum(bvc_t *c, bvnode_t i, bvc_sum_t *p) {
  uint32_t j, m, nbits;
  node_occ_t n;
  thvar_t x, y;
  bool all_neg;

  assert(p->len >= 3);

  nbits = p->header.bitsize;
  m = p->len;
  n = p->sum[0];
  x = bvc_dag_get_var_of_leaf(&c->dag, n);
  all_neg = (sign_of_occ(n) != 0);

  /*
   * Invariant:
   * - all_neg means that all node occurrences
   *   in 0 ... j-1 have negative sign.
   * - if all_neg is true, then x is the opposite
   *   if (sum n0 ... n_{j-1})
   *   otherwise, x is (sum n0 ... n_{j-1}
   */
  for (j=1; j<m; j++) {
    n = p->sum[j];
    y = bvc_dag_get_var_of_leaf(&c->dag, n);
    if (all_neg) {
      if (sign_of_occ(n) == 0) {
        x = bv_compiler_mk_bvsub(c, nbits, y, x);
        all_neg = false;
      } else {
        x = bv_compiler_mk_bvadd(c, nbits, x, y);
      }
    } else {
      if (sign_of_occ(n) == 0) {
        x = bv_compiler_mk_bvadd(c, nbits, x, y);
      } else {
        x = bv_compiler_mk_bvsub(c, nbits, x, y);
      }
    }
  }

  if (all_neg) {
    x = bv_compiler_mk_bvneg(c, nbits, x);
  }

  // replace i by [leaf x] in DAG
  bvc_dag_convert_to_leaf(&c->dag, i, x);
}


/*
 * Process node i:
 * - if it's simple, node i is compiled and moved to the list of leaves
 * - otherwise, node i is moved to the auxiliary list (in c->dag)
 */
static void bvc_process_node_if_simple(bvc_t *c, bvnode_t i) {
  bvc_dag_t *dag;
  bvc_prod_t *p;
  bvc_sum_t *s;

  dag = &c->dag;
  switch (bvc_dag_node_type(dag, i)) {
  case BVC_OFFSET:
  case BVC_MONO:
    break; // skip it

  case BVC_PROD:
    p = bvc_dag_node_prod(dag, i);
    if (bvc_prod_is_simple(dag, p)) {
      bvc_process_simple_prod(c, i, p);
      return;
    }
    break;

  case BVC_SUM:
    s = bvc_dag_node_sum(dag, i);
    if (bvc_sum_is_simple(dag, s)) {
      bvc_process_simple_sum(c, i, s);
      return;
    }
    break;

  case BVC_LEAF:
  case BVC_ALIAS:
  case BVC_ZERO:
  case BVC_CONSTANT:
    assert(false);
    break;
  }

  /*
   * i not touched: remove it from the complex-node list
   */
  bvc_move_node_to_aux_list(dag, i);
}



/*
 * COMPILATION
 */

/*
 * Convert all elementary nodes
 */
static void bv_compiler_convert_elem_nodes(bvc_t *c) {
  bvnode_t j;

  /*
   * Note: bvc_process_elem_node removes j from the elementary node list
   * so we always get the first element of the leaf list until it's empty
   */
  for (;;) {
    j = bvc_first_elem_node(&c->dag);
    if (j < 0) break;
    bvc_process_elem_node(c, j);

#if TRACE
    printf("\n=== After compiling node n%"PRId32" =====\n", j);
    print_bvc_dag(stdout, &c->dag);
    fflush(stdout);
#endif
  }
}


/*
 * Convert all simple nodes
 */
static void bv_compiler_convert_simple_nodes(bvc_t *c) {
  bvnode_t j;

  for (;;) {
    j = bvc_first_complex_node(&c->dag);
    if (j < 0) break;
    bvc_process_node_if_simple(c, j);

#if TRACE
    printf("\n=== After compiling node n%"PRId32" =====\n", j);
    print_bvc_dag(stdout, &c->dag);
    fflush(stdout);
#endif

  }
  // move back all aux nodes to the complex list
  bvc_move_aux_to_complex_list(&c->dag);
}


/*
 * Auxiliary function: create (bvneg x) if it doesn't exist
 * already.
 * TODO: check for (bvneg (bvneg z)) and other simplifications?
 */
static thvar_t bv_compiler_get_bvneg(bvc_t *c, thvar_t x) {
  thvar_t y;
  uint32_t nbits;

  assert(0 < x && x < c->vtbl->nvars);
  y = find_bvneg(c->vtbl, x);
  if (y < 0) {
    nbits = bvvar_bitsize(c->vtbl, x);
    y = bv_compiler_mk_bvneg(c, nbits, x);
  }

  return y;
}


/*
 * Get the variable y that x is compiled to
 * - store the mapping [x --> y] in the vmap
 */
static void bv_compiler_store_mapping(bvc_t *c, thvar_t x) {
  int_hmap_pair_t *p;
  node_occ_t r;
  thvar_t y;
  uint32_t sign;

  assert(0 < x && x < c->vtbl->nvars);

  p = int_hmap_get(&c->cmap, x);
  if (p->val >= 0) {
    // x is already compiled (to a constant)
    assert(p->val != x);
    return;
  }

  r  = bvc_dag_nocc_of_var(&c->dag, x); // node occurrence mapped to x
  y = bvc_dag_get_nocc_compilation(&c->dag, r); // r is compiled to y
  assert(y >= 0);

  /*
   * y is a pair (variable + sign)
   * if the sign is negative, x is mapped to (bvneg variable)
   * if the sign is positive, x is mapped to variable
   */
  sign = (y & 1);
  y >>= 1;
  assert(bvvar_bitsize(c->vtbl, x) == bvvar_bitsize(c->vtbl, y));
  if (sign != 0) {
    y = bv_compiler_get_bvneg(c, y);
  }
  assert(0 < y && y < c->vtbl->nvars && x != y);
  p->val = y;
}


void bv_compiler_process_queue(bvc_t *c) {
  uint32_t i, n;

  n = c->queue.top;
  for (i=0; i<n; i++) {
    bv_compiler_map_var_to_dag(c, c->queue.data[i]);
  }

#if TRACE
  printf("\n==== INIITIAL DAG ====\n");
  print_bvc_dag(stdout, &c->dag);
#endif

  // try to simplify the DAG nodes using existing elementary expressions
  n = c->elemexp.top;
  for (i=0; i<n; i++) {
    bv_compiler_simplify_dag(c, c->elemexp.data[i]);;
  }


  // compile the rest until the complex-node list is empty
  for (;;) {
    bv_compiler_convert_elem_nodes(c);
    bv_compiler_convert_simple_nodes(c);
    bv_compiler_convert_elem_nodes(c);

    assert(bvc_first_elem_node(&c->dag) < 0);
    if (bvc_first_complex_node(&c->dag) < 0) break;

#if TRACE
    printf("\n==== FORCING ELEM NODES ====\n");
    print_bvc_dag(stdout, &c->dag);
    fflush(stdout);
#endif

    bvc_dag_force_elem_node(&c->dag);

#if TRACE
    printf("\n==== AFTER FORCING ====\n");
    print_bvc_dag(stdout, &c->dag);
    fflush(stdout);
#endif
  }


  /*
   * Collect the compilation results
   */
  n = c->queue.top;
  for (i=0; i<n; i++) {
    bv_compiler_store_mapping(c, c->queue.data[i]);
  }


  /*
   * Cleanup
   */
  reset_bvc_queue(&c->queue);
  reset_bvc_dag(&c->dag);
  reset_int_bvset(&c->in_queue);
}
