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

  init_bvc_queue(&c->queue);
  init_int_bvset(&c->in_queue, 0);

  init_bvconstant(&c->aux);
}


/*
 * Delete
 */
void delete_bv_compiler(bvc_t *c) {
  delete_int_hmap(&c->cmap);
  delete_bvc_queue(&c->elemexp);

  delete_bvc_queue(&c->queue);
  delete_int_bvset(&c->in_queue);

  delete_bvconstant(&c->aux);
}

/*
 * Empty
 */
void reset_bv_compiler(bvc_t *c) {
  int_hmap_reset(&c->cmap);
  reset_bvc_queue(&c->elemexp);

  reset_bvc_queue(&c->queue);
  reset_int_bvset(&c->in_queue);
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
 * COMPILATION PHASE 2
 */

/*
 * In this phase; scan c->queue:
 * - any x in the queue that has a non-ambiguous definition
 *   is compiled immediately
 * - the other are TBD
 */

/*
 * Check whether x is a leaf in the compilation DAG
 * - x is a leaf if it's not a polynomial or if it's already compiled
 */
static bool bvvar_is_leaf(bvc_t *c, thvar_t x) {
  switch (bvvar_tag(c->vtbl, x)) {
  case BVTAG_POLY64:
  case BVTAG_POLY:
  case BVTAG_PPROD:
    return bvvar_is_compiled(c, x);;

  default:
    return true;
  }
}


/*
 * Constructors for monomials (a * x)
 * - n = number of bits
 * - a = coefficient
 * - x = variable
 * - a must be normalized modulo 2^n
 *
 * Depending on a, this gets turned into one of the following expressions:
 * - if a is +1  -->  x
 * - if a is -1  --> (BVNEG x)
 * - otherwise   --> (BVMUL a x) or (BVNEG (BVMUL -a x))
 *   depending on the number of '1' bits in a and -a
 *
 * Heuristics:
 * - the number of adders required for (a * x) is equal to the number of '1'
 *   bits in a (i.e., to popcount(a)).
 * - (BVMUL a x) has cost equal to popcount(a)
 *   (BVNEG (BVMUL -a x)) has cost equal to  popcount(-a) + 1 (we count
 *    BVNEG as one more adder)
 *
 *
 * NOTE: there are better techniques
 * - could use a signed digit representation for the constant a
 * - if there are several monomials (a_0 x) ... (a_t x), then
 *   there are optimizations used in digital filter circuits:
 * 
 * Reference: 
 *  Dempster & McLeod, Constant integer multiplication using minimum adders, 
 *  IEE Proceedings, Cicuits, Devices & Systems, vol. 141, Issue 5, pp. 407-413,
 *  October 1994
 */
static thvar_t bv_compiler_mk_mono64(bvc_t *c, uint32_t n, uint64_t a, thvar_t x) {
  uint64_t b;
  thvar_t y;
  
  assert(1 <= n && n <= 64 && a == norm64(a, n));

  if (a == 1) {
    // (a * x) --> x
    y = x;
  } else if (a == mask64(n)) { 
    // (-1 * x) --> (bvneg x)
    y = bv_compiler_mk_bvneg(c, n, x);
  } else {
    b = norm64(-a, n);

    assert(1 <= popcount64(a) && popcount64(a) < n &&
	   1 <= popcount64(b) && popcount64(b) < n);

    if (popcount64(b) + 1 < popcount64(a)) {
      // (a * x) --> (bvneg (bvmul b x))
      y = get_bvconst64(c->vtbl, n, b);
      y = bv_compiler_mk_bvmul(c, n, y, x);
      y = bv_compiler_mk_bvneg(c, n, y);
    } else {
      // (a * x) --> (bvmul a x)
      y = get_bvconst64(c->vtbl, n, a);
      y = bv_compiler_mk_bvmul(c, n, y, x);
    }
  }

  return y;
}

static thvar_t bv_compiler_mk_mono(bvc_t *c, uint32_t n, uint32_t *a, thvar_t x) {
  bvconstant_t *aux;
  thvar_t y;
  uint32_t w;

  assert(n > 64 && bvconst_is_normalized(a, n));

  w = (n + 31) >> 5; // number of words in a
  if (bvconst_is_one(a, w)) {
    y = x;
  } else if (bvconst_is_minus_one(a, n)) {
    y = bv_compiler_mk_bvneg(c, n, x);
  } else {
    // store -a in c->aux
    aux = &c->aux;
    bvconstant_copy(aux, n, a);
    bvconstant_negate(aux);
    bvconstant_normalize(aux);

    if (bvconst_popcount(aux->data, w) + 1 < bvconst_popcount(a, w)) {
      y = get_bvconst(c->vtbl, n, aux->data);
      y = bv_compiler_mk_bvmul(c, n, y, x);
      y = bv_compiler_mk_bvneg(c, n, y);
    } else {
      y = get_bvconst(c->vtbl, n, a);
      y = bv_compiler_mk_bvmul(c, n, y, x);
    }
  }

  return y;
}



/*
 * Constructors for a + x and a - x
 * - n = number of bits
 * - a = constant (must be non-zero)
 * - x = variable
 * - a must be normalized modulo 2^n
 */
static thvar_t bv_compiler_mk_const64_plus_var(bvc_t *c, uint32_t n, uint64_t a, thvar_t x) {
  thvar_t k;

  assert(1 <= n && n <= 64 && a == norm64(a, n));

  k = get_bvconst64(c->vtbl, n, a);
  return bv_compiler_mk_bvadd(c, n, k, x);
}

static thvar_t bv_compiler_mk_const64_minus_var(bvc_t *c, uint32_t n, uint64_t a, thvar_t x) {
  thvar_t k;

  assert(1 <= n && n <= 64 && a == norm64(a, n));

  k = get_bvconst64(c->vtbl, n, a);
  return bv_compiler_mk_bvsub(c, n, k, x);
}


static thvar_t bv_compiler_mk_const_plus_var(bvc_t *c, uint32_t n, uint32_t *a, thvar_t x) {
  thvar_t k;

  assert(n > 64 && bvconst_is_normalized(a, n));

  k = get_bvconst(c->vtbl, n, a);
  return bv_compiler_mk_bvadd(c, n, k, x);
}

static thvar_t bv_compiler_mk_const_minus_var(bvc_t *c, uint32_t n, uint32_t *a, thvar_t x) {
  thvar_t k;

  assert(n > 64 && bvconst_is_normalized(a, n));

  k = get_bvconst(c->vtbl, n, a);
  return bv_compiler_mk_bvsub(c, n, k, x);
}



#if 0


/*
 * Compile polynomial p if it's unambiguous
 * - return y such that y = compilation of p if so
 * - return null_thvar (i.e., -1) otherwise (i.e., p's compilation is delayed to phase 3)
 */
static thvar_t simple_bvpoly64(bvc_t *c, bvpoly64_t *p) {
  thvar_t y, x;
  uint32_t n;

  assert(p->nterms > 0);

  y = null_thvar;
  switch (p->nterms) {
  case 1:
    n = p->bitsize;
    x = p->mono[0].var;
    assert(x != const_idx && p->mono[0].coeff != 1);
    if (bvvar_is_leaf(c, x)) {
      y = bv_compiler_mk_mono64(c, n, p->mono[0].coeff, x);
    }
    break;

  case 2:
    n = p->bitsize;
    
    break;

  default:
    break;
  }

  return y;
}


/*
 * Process polynomial p
 * - x = variable whose definition is p
 */
static void bv_compiler_phase2_process_poly64(bvc_t *c, thvar_t x, bvpoly64_t *p) {
  
}


#endif
