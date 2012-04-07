/*
 * SUPPORT FOR CONVERTING BIT-VECTOR POLYNOMIALS
 * TO ELEMENTATY EXPRESSSIONS.
 */

#include <assert.h>

#include "bit_tricks.h"
#include "bv64_constants.h"
#include "bvpoly_compiler.h"


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
 * - mtbl = attahced merge table
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
 * In all constructors:
 * - n = number of bits
 * - x (and y) = operands
 */
static thvar_t bv_compiler_mk_bvadd(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);

  // normalize: left operand <= right operand
  if (x > y) {
    v = x; x = y; y = v;
  }

  assert(find_bvadd(c->vtbl, x, y) == -1); // not already present

  v = get_bvadd(c->vtbl, n, x, y);
  bvc_queue_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_bvsub(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);
  assert(find_bvsub(c->vtbl, x, y) == -1); // not already present

  v = get_bvsub(c->vtbl, n, x, y);
  bvc_queue_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_bvmul(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);

  // normalize: left operand <= right operand
  if (x > y) {
    v = x; x = y; y = v;
  }

  assert(find_bvmul(c->vtbl, x, y) == -1); // not already present

  v = get_bvmul(c->vtbl, n, x, y);
  bvc_queue_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_bvneg(bvc_t *c, uint32_t n, thvar_t x) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars);
  assert(find_bvneg(c->vtbl, x) == -1);

  v = get_bvneg(c->vtbl, n, x);
  bvc_queue_push(&c->elemexp, v);

  return v;
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
 * Add x to the queue and to in_queue
 */
static void push_to_process(bvc_t *c, thvar_t x) {
  bvc_queue_push(&c->queue, x);
  int_bvset_add(&c->in_queue, x);
}


/*
 * Add variable x to the internal queue
 * - also recursively add all the children of x
 * - the children precede x in c->queue
 */
static void bv_compiler_push_poly64(bvc_t *c, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i = 1;
  }
  while (i < n) {
    bv_compiler_push_var(c, p->mono[i].var);
    i ++;
  }
}

static void bv_compiler_push_poly(bvc_t *c, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i = 1;
  }
  while (i < n) {
    bv_compiler_push_var(c, p->mono[i].var);
    i ++;
  }
}

static void bv_compiler_push_pprod(bvc_t *c, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    bv_compiler_push_var(c, p->prod[i].var);
  }
}

void bv_compiler_push_var(bvc_t *c, thvar_t x) {
  bv_vartable_t *vtbl;
  
  assert(0 < x && x < c->vtbl->nvars);

  vtbl = c->vtbl;

  // apply root substitution
  x = mtbl_get_root(c->mtbl, x);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_POLY64:
    if (bvvar_to_process(c, x)) {
      bv_compiler_push_poly64(c, bvvar_poly64_def(vtbl, x));
      push_to_process(c, x);
    }
    break;

  case BVTAG_POLY: 
    if (bvvar_to_process(c, x)) {
      bv_compiler_push_poly(c, bvvar_poly_def(vtbl, x));
      push_to_process(c, x);
    }
    break;

  case BVTAG_PPROD:
    if (bvvar_to_process(c, x)) {
      bv_compiler_push_pprod(c, bvvar_pprod_def(vtbl, x));
      push_to_process(c, x);
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
static node_occ_t bv_compiler_poly64_to_dag(bvc_t *c, bvpoly64_t *p) {
  bvc_dag_t *dag;
  ivector_t *v;
  uint32_t i, n, nbits;
  thvar_t x;
  node_occ_t q;

  dag = &c->dag;

  v = &c->buffer;
  ivector_reset(v);

  n = p->nterms;
  nbits = p->bitsize;

  i = 0;
  if (p->mono[i].var == const_idx) {
    ivector_push(v, const_idx); // need a place-holder in v->data[0]
    i = 1;
  }
  while (i < n) {
    x = mtbl_get_root(c->mtbl, p->mono[i].var);
    q = bvc_dag_get_nocc_of_var(dag, x, nbits);
    ivector_push(v, q);
    i++;
  }

  return bvc_dag_poly64(dag, p, v->data);
}


static node_occ_t bv_compiler_poly_to_dag(bvc_t *c, bvpoly_t *p) {
  bvc_dag_t *dag;
  ivector_t *v;
  uint32_t i, n, nbits;
  thvar_t x;
  node_occ_t q;

  dag = &c->dag;

  v = &c->buffer;
  ivector_reset(v);

  n = p->nterms;
  nbits = p->bitsize;

  i = 0;
  if (p->mono[i].var == const_idx) {
    ivector_push(v, const_idx); // need a place-holder in v->data[0]
    i = 1;
  }
  while (i < n) {
    x = mtbl_get_root(c->mtbl, p->mono[i].var);
    q = bvc_dag_get_nocc_of_var(dag, x, nbits);
    ivector_push(v, q);
    i++;
  }

  return bvc_dag_poly(dag, p, v->data);
}


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
    q = bvc_dag_get_nocc_of_var(dag, x, bitsize);
    ivector_push(v, q);
  }

  return bvc_dag_pprod(dag, p, v->data, bitsize);
}



/*
 * Build a DAG node for x and store the mapping [x --> node]
 * - x must be a polynomial or a power product
 */
static void bv_compiler_map_var_to_dag(bvc_t *c, thvar_t x) {
  bv_vartable_t *vtbl;
  node_occ_t q;

  assert(0 < x && x < c->vtbl->nvars);

  q = -1; // Stop GCC warning

  vtbl = c->vtbl;

  x = mtbl_get_root(c->mtbl, x);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_POLY64:
    q = bv_compiler_poly64_to_dag(c, bvvar_poly64_def(vtbl, x));
    break;

  case BVTAG_POLY:
    q = bv_compiler_poly_to_dag(c, bvvar_poly_def(vtbl, x));
    break;

  case BVTAG_PPROD:
    q = bv_compiler_pprod_to_dag(c, bvvar_pprod_def(vtbl, x), bvvar_bitsize(vtbl, x));
    break;

  default:
    assert(false);
    break;
  }

  bvc_dag_map_var(&c->dag, x, q);  
}


/*
 * FOR TESTING ONLY
 */
void bv_compiler_process_queue(bvc_t *c) {
  uint32_t i, n;

  n = c->queue.top;
  for (i=0; i<n; i++) {
    bv_compiler_map_var_to_dag(c, c->queue.data[i]);
  }
}
