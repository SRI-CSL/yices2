/*
 * Bit-vector arithmetic expressions:
 * - polynomials with integer-valued coefficients 
 * - coefficients are bvarith_constants
 */

#include "bvarith_expr.h"
#include "memalloc.h"
#include "hash_functions.h"


/*
 * Initialize a list store
 */
void init_bvmlist_store(object_store_t *s) {
  init_objstore(s, sizeof(bvmlist_t), BVMBANK_SIZE);
}


/*
 * Delete the store. All buffers attached to that store must be deleted first.
 * It's not possible to determine which coefficients are 64bits and which
 * are pointers. So we can't use finalization here.
 */
void delete_bvmlist_store(object_store_t *s) {
  delete_objstore(s);
}


/*
 * Initialize buffer b.
 * - m = attached polynomial manager
 * - s = attached store
 * - b cannot be used for any operation yet, because the coefficient size
 *   is not known.
 */
void init_bvarith_buffer(bvarith_buffer_t *b, bv_var_manager_t *m, object_store_t *s) {
  bvmlist_t *start, *end;

  end = (bvmlist_t *) objstore_alloc(s);
  end->next = NULL;
  end->var = max_idx;
  end->coeff.c = 0;

  start = (bvmlist_t *) objstore_alloc(s);
  start->next = end;
  start->var = null_idx;
  start->coeff.c = 0;
  
  b->nterms = 0;
  b->size = 0;
  b->width = 0;

  b->list = start;
  b->store = s;
  b->manager = m;
}

/*
 * Clear b: reset size and width, empty the list.
 * Keep the start and end markers.
 */
static void bvarith_buffer_clear(bvarith_buffer_t *b) {
  bvmlist_t *p, *next;
  uint32_t k;

  k = b->width;
  p = b->list->next; // skip start
  if (k > 2) {
    while (p->var < max_idx) {
      next = p->next;
      bvconst_free(p->coeff.ptr, k);
      objstore_free(b->store, p);
      p = next;
    }
  } else {
    while (p->var < max_idx) {
      next = p->next;
      objstore_free(b->store, p);
      p = next;
    }
  }

  // p is end marker
  b->list->next = p;

  b->nterms = 0;
  b->size = 0;
  b->width = 0;
}

/*
 * Delete b
 */
void delete_bvarith_buffer(bvarith_buffer_t *b) {
  bvmlist_t *start, *end;

  bvarith_buffer_clear(b);
  start = b->list;
  end = b->list->next;

  objstore_free(b->store, start);
  objstore_free(b->store, end);

  b->list = NULL;
  b->store = NULL;
  b->manager = NULL;
}


/*
 * Prepare buffer b: set bit size equal to n
 */
void bvarith_buffer_prepare(bvarith_buffer_t *b, uint32_t n) {
  uint32_t w;

  assert(n > 0);
  if (b->size != 0) {
    bvarith_buffer_clear(b);
  }

  w = (n + 31) >> 5;
  b->size = n;
  b->width = w;
}


/*
 * Normalize the coefficients (modulo 2^size)
 * Remove monomials with zero coefficients
 */
static void wide_buffer_normalize(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;
  uint32_t n, k;

  assert(b->width > 2);

  q = b->list;
  p = q->next;
  n = b->size;
  k = b->width;

  while (p->var < max_idx) {
    bvconst_normalize(p->coeff.ptr, n);
    if (bvconst_is_zero(p->coeff.ptr, k)) {
      q->next = p->next;
      bvconst_free(p->coeff.ptr, k);
      objstore_free(b->store, p);
      b->nterms --;
      p = q->next;
    } else {
      q = p;
      p = q->next;
    }
  }
}

/*
 * Note: if x is uint64_t then shift operations
 * x << n and x >> n  are undefined if n<0 or n>=64.
 * So setting mask = (1 << n) - 1 does not work.
 */
static void narrow_buffer_normalize(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;
  uint32_t n;
  uint64_t mask;

  assert(b->width <= 2);
  assert(b->size > 0 && b->size <= 64);

  n = b->size;
  mask = (~((uint64_t) 0)) >> (64 - n);

  q = b->list;
  p = q->next;

  while (p->var < max_idx) {
    p->coeff.c &= mask; // clear high-order bits
    if (p->coeff.c == 0) {
      q->next = p->next;
      objstore_free(b->store, p);
      b->nterms --;
      p = q->next;
    } else {
      q = p;
      p = q->next;
    }
  }
}

void bvarith_buffer_normalize(bvarith_buffer_t *b) {
  if (b->width <= 2) {
    narrow_buffer_normalize(b); 
  } else {
    wide_buffer_normalize(b);
  }
}


/*
 * Construct a bvarith term from b and reset b
 * - b must be normalized
 */
bvarith_expr_t *bvarith_buffer_get_expr(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;
  bvarith_expr_t *expr;
  object_store_t *s;
  int32_t i, n;
  
  n = b->nterms;
  expr = (bvarith_expr_t *) safe_malloc(sizeof(bvarith_expr_t) + (n + 1) * sizeof(bvmono_t));
  expr->nterms = n;
  expr->size = b->size;
  expr->width = b->width;

  s = b->store;
  i = 0;
  p = b->list->next;
  while (p->var < max_idx) {
    q = p->next;
    expr->mono[i].var = p->var;
    expr->mono[i].coeff = p->coeff; // shallow copy.
    // free element p
    objstore_free(s, p);
    p = q;
    i ++;
  }

  // restore list
  b->list->next = p;
  b->nterms = 0;

  // set end marker in expr
  expr->mono[i].var = max_idx;
  expr->mono[i].coeff.c = 0;
  
  return expr;
}


/*
 * Hash code.
 * - b must be normalized.
 */
uint32_t bvarith_buffer_hash(bvarith_buffer_t *b) {
  bvmlist_t *p;
  bv_var_t v;
  uint32_t h, k;

  h = 0xa453baf4; // seed
  k = b->width;
  p = b->list->next;
  v = p->var;

  if (k > 2) {

    while (v < max_idx) {
      h = jenkins_hash_intarray_var(k, (int32_t *) p->coeff.ptr, h);
      h = jenkins_hash_mix2(v, h);

      p = p->next;
      v = p->var;
    }

  } else {

    while (v < max_idx) {
      h = jenkins_hash_triple(v, (int32_t) p->coeff.c, (int32_t)(p->coeff.c >> 32), h);
      p = p->next;
      v = p->var;
    }
  }
  return h;
}


/*
 * Hash code of expression e
 */
uint32_t bvarith_expr_hash(bvarith_expr_t *e) {
  bvmono_t *p;
  bv_var_t v;
  uint32_t h, k;

  h = 0xa453baf4; // seed
  k = e->width;
  p = e->mono;
  v = p->var;

  if (k > 2) {

    while (v < max_idx) {
      h = jenkins_hash_intarray_var(k, (int32_t *) p->coeff.ptr, h);
      h = jenkins_hash_mix2(v, h);

      p ++;
      v = p->var;
    }

  } else {

    while (v < max_idx) {
      h = jenkins_hash_triple(v, (int32_t) p->coeff.c, (int32_t)(p->coeff.c >> 32), h);
      p ++;
      v = p->var;
    }
  }
  return h;
}


/*
 * Comparison between buffer b and bv-expression e
 * - b and e must be normalized
 */
bool bvarith_buffer_equal_expr(bvarith_buffer_t *b, bvarith_expr_t *e) {
  uint32_t k;  
  bvmono_t *aux;
  bvmlist_t *p;
  bv_var_t v, v1;

  if (e->nterms != b->nterms || e->size != b->size) {
    return false;
  }

  k = b->width;
  assert(k == e->width);

  aux = e->mono;
  v1 = aux->var;  
  p = b->list->next;
  v = p->var;
  while (v == v1) {
    if (v == max_idx) return true;

    if ((k <= 2 && p->coeff.c != aux->coeff.c) 
	|| (k > 2 && bvconst_neq(p->coeff.ptr, aux->coeff.ptr, k))) {
      return false;
    }

    p = p->next;
    v = p->var;
    aux ++;
    v1 = aux->var;
  }

  return false;
}



/*
 * Comparison between buffers b and b1
 * - b and b1 must be normalized
 */
bool bvarith_buffer_equal_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  uint32_t k;
  bvmlist_t *p, *p1;
  bv_var_t v, v1;

  if (b1->nterms != b->nterms || b1->size != b->size) {
    return false;
  }

  k = b->width;  

  p = b->list->next;
  v = p->var;
  p1 = b1->list->next;
  v1 = p1->var;
  while (v == v1) {
    if (v == max_idx) return true;

    if ((k <= 2 && p->coeff.c != p1->coeff.c) 
	|| (k > 2 && bvconst_neq(p->coeff.ptr, p1->coeff.ptr, k))) {
      return false;
    }

    p = p->next;
    v = p->var;
    p1 = p1->next;
    v1 = p1->var;
  }

  return false;
}




/*
 * Auxiliary functions: compare two arrays of bvmononials of same bitsize.
 */
// narrow arrays 
static bool narrow_bvmonarray_equal(bvmono_t *b1, bvmono_t *b2) {
  bv_var_t v1, v2;

  v1 = b1->var;
  v2 = b2->var;
  while (v1 == v2) {
    if (v1 == max_idx) return true;
    if (b1->coeff.c != b2->coeff.c) return false;

    b1++;
    v1 = b1->var;
    b2++;
    v2 = b2->var;
  }

  return false;
}

// wide arrays: width = k
static bool wide_bvmonarray_equal(bvmono_t *b1, bvmono_t *b2, uint32_t k) {
  bv_var_t v1, v2;

  v1 = b1->var;
  v2 = b2->var;
  while (v1 == v2) {
    if (v1 == max_idx) return true;
    if (bvconst_neq(b1->coeff.ptr, b2->coeff.ptr, k)) return false;

    b1++;
    v1 = b1->var;
    b2++;
    v2 = b2->var;
  }

  return false;
}


/*
 * Comparison between two bv-expressions: both must be normalized
 */
bool bvarith_expr_equal_expr(bvarith_expr_t *e1, bvarith_expr_t *e2) {
  uint32_t k;

  if (e1->nterms != e2->nterms || e1->size != e2->size) {
    return false;
  }

  k = e1->width;
  assert(k == e2->width);
  if (k <= 2) {
    return narrow_bvmonarray_equal(e1->mono, e2->mono);
  } else {
    return wide_bvmonarray_equal(e1->mono, e2->mono, k);
  }
}



/*
 * Check whether two bv-expressions are trivially disequal:
 * i.e., whether e1 - e2 is a non-zero constant.
 */
bool bvarith_must_disequal_expr(bvarith_expr_t *e1, bvarith_expr_t *e2) {
  uint32_t k;
  bvmono_t *b1, *b2;
  bv_var_t v1, v2;

  assert(e1->size == e2->size);

  k = e1->width;
  assert(k == e2->width);

  b1 = e1->mono;
  v1 = b1->var;
  b2 = e2->mono;
  v2 = b2->var;

  if (v1 != const_idx && v2 != const_idx) {
    // both constant terms in e1 and e2 are zero
    return false;
  }

  if (v1 == const_idx && v2 == const_idx) {
    if ((k <= 2 && b1->coeff.c == b2->coeff.c)
	|| (k > 2 && bvconst_eq(b1->coeff.ptr, b2->coeff.ptr, k))) {
      // both constant terms are equal
      return false;
    }
  }

  // skip constant terms
  if (v1 == const_idx) b1 ++;
  if (v2 == const_idx) b2 ++;

  // check whether the remaining terms are equal
  if (k <= 2) {
    return narrow_bvmonarray_equal(b1, b2);
  } else {
    return wide_bvmonarray_equal(b1, b2, k);
  }
}







/*
 * Check whether b is a constant polynomial
 */
bool bvarith_buffer_is_constant(bvarith_buffer_t *b) {
  int32_t n;

  n = b->nterms;
  return (n == 0) || (n == 1 && b->list->next->var == const_idx);
}


/*
 * Extract constant of b and reset b: two variants
 */
uint64_t bvarith_buffer_get_constant64(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;
  uint64_t c;

  assert(bvarith_buffer_is_constant(b));
  assert(b->width <= 2);

  p = b->list->next;
  if (p->var == const_idx) {
    c = p->coeff.c;
    q = p->next;
    objstore_free(b->store, p);

    assert(q->var == max_idx);;
    b->list->next = q;
    b->nterms = 0;
    return c;

  } else {
    assert(b->nterms == 0);
    return 0;
  }
}


uint32_t *bvarith_buffer_get_constant(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;
  uint32_t *c, k;

  assert(bvarith_buffer_is_constant(b));
  assert(b->width > 2);

  p = b->list->next;
  if (p->var == const_idx) {
    c = p->coeff.ptr;
    q = p->next;
    objstore_free(b->store, p);

    assert(q->var == max_idx);
    b->list->next = q;
    b->nterms = 0;
    return c;

  } else {
    k = b->width;
    c = bvconst_alloc(k);
    bvconst_clear(c, k);
    return c;
  }
  
}


/*
 * Store value of constant b into c
 * b must be normalized.
 */
void bvarith_buffer_copy_constant(bvarith_buffer_t *b, bvconstant_t *c) {
  bvmlist_t *p, *q;
  uint32_t k;

  assert(bvarith_buffer_is_constant(b));

  k = b->width;
  p = b->list->next;

  bvconstant_set_bitsize(c, b->size);
  if (p->var == const_idx) {
    if (k <= 2) {
      bvconst_set64(c->data, k, p->coeff.c);
    } else {
      bvconst_set(c->data, k, p->coeff.ptr);
      bvconst_free(p->coeff.ptr, k);
    }
    q = p->next;
    objstore_free(b->store, p);

    assert(q->var == max_idx);
    b->list->next = q;
    b->nterms = 0;    
  } else {
    bvconst_clear(c->data, k);
  }
}


/*
 * Check whether b is reduced to a variable.
 * - b must be normalized.
 */
bool bvarith_buffer_is_variable(bvarith_buffer_t *b) {
  uint32_t k;
  bvmlist_t *p;

  p = b->list->next;
  if (b->nterms == 1 && p->var != const_idx) {
    k = b->width;
    if (k > 2) {
      return bvconst_is_one(p->coeff.ptr, k);
    } else {
      return p->coeff.c == 1;
    }
  }

  return false;
}


/*
 * Degree of an arithmetic expression
 * If the expression is zero, return 0.
 */
int32_t bvarith_expr_degree(bvarith_expr_t *p, bv_var_manager_t *m) {
  int32_t n;
  bv_var_t v;

  n = p->nterms;
  if (n == 0) {
    return 0;
  }

  v = p->mono[n - 1].var;
  return polymanager_var_degree(&m->pm, v);
}


/*
 * Degree of a bvarith_buffer b
 * If the expression is zero, return 0.
 */
int32_t bvarith_buffer_degree(bvarith_buffer_t *b) {
  bvmlist_t *p;
  bv_var_t v;

  p = b->list;
  do {
    v = p->var;
    p = p->next;
  } while (p->var < max_idx);

  if (v == null_idx) {
    return 0; 
  } else {
    return polymanager_var_degree(&b->manager->pm, v);
  }
}



/*
 * Store all variables of p in vector u
 */
void bvarith_expr_get_vars(bvarith_expr_t *p, bv_var_manager_t *m, ivector_t *u) {
  int32_t i, n;

  ivector_reset(u);
  n = p->nterms;
  for (i=0; i<n; i++) {
    bv_var_manager_get_vars(m, p->mono[i].var, u); 
  }
  ivector_remove_duplicates(u);
}


/*
 * Store the terms attached to variables of p in vector u
 */
void bvarith_expr_get_terms(bvarith_expr_t *p, bv_var_manager_t *m, ivector_t *u) {
  int32_t i, n;

  ivector_reset(u);
  n = p->nterms;
  for (i=0; i<n; i++) {
    bv_var_manager_get_terms(m, p->mono[i].var, u); 
  }
  ivector_remove_duplicates(u);
}





/****************
 *  ARITHMETIC  *
 ***************/

/*
 * Initialize/set b to 1
 */
void bvarith_buffer_set_one(bvarith_buffer_t *b) {
  uint32_t k, n;
  bvmlist_t *p, *q;

  assert(b->size > 0);
  n = b->size;
  k = b->width;
  if (b->nterms > 0) {
    // reset b
    bvarith_buffer_clear(b);
    b->size = n;
    b->width = k;
  }

  q = b->list;

  p = (bvmlist_t *) objstore_alloc(b->store);
  p->var = const_idx;
  p->next = q->next;
  if (k <= 2) {
    p->coeff.c = 1;
  } else {
    p->coeff.ptr = bvconst_alloc(k);
    bvconst_set_one(p->coeff.ptr, k);
  }

  // add p at the start of b's list
  q->next = p;
  b->nterms = 1;
}


/*
 * Initialize/set b to -1
 */
void bvarith_buffer_set_minus_one(bvarith_buffer_t *b) {
  uint32_t k, n;
  bvmlist_t *p, *q;

  assert(b->size > 0);
  n = b->size;
  k = b->width;
  if (b->nterms > 0) {
    // reset b
    bvarith_buffer_clear(b);
    b->size = n;
    b->width = k;
  }

  q = b->list;

  p = (bvmlist_t *) objstore_alloc(b->store);
  p->var = const_idx;
  p->next = q->next;
  if (k <= 2) {
    p->coeff.c = (~((uint64_t) 0)) >> (64 - n);
  } else {
    p->coeff.ptr = bvconst_alloc(k);
    bvconst_set_minus_one(p->coeff.ptr, k);
    bvconst_normalize(p->coeff.ptr, n);
  }

  // add p at the start of b's list
  q->next = p;
  b->nterms = 1;
}







/*
 * Compute opposite of b.
 */
void bvarith_buffer_negate(bvarith_buffer_t *b) {
  uint32_t k;
  bvmlist_t *p;

  k = b->width;
  p = b->list->next;
  if (k <= 2) {
    while (p->var < max_idx) {
      p->coeff.c = - p->coeff.c;
      p = p->next;
    }
  } else {
    while (p->var < max_idx) {
      bvconst_negate(p->coeff.ptr, k);
      p = p->next;
    }
  }
}




/*
 * Add monomial a * v to b
 */
void bvarith_buffer_add_mono(bvarith_buffer_t *b, bv_var_t v, uint32_t *a) {
  uint32_t k;
  uint64_t c;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;  

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  k = b->width;
  if (bvconst_is_zero(a, k)) return;

  c = a[0]; 
  if (k == 2) {
    c += ((uint64_t) a[1]) << 32;
  }

  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    if (k > 2) {
      bvconst_add(p->coeff.ptr, k, a);
    } else {
      p->coeff.c += c;
    }
  } else {
    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->var = v;
    aux->next = p;
    if (k > 2) {
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_set(aux->coeff.ptr, k, a);
    } else {
      aux->coeff.c = c;
    }
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add monomial - a * v to b
 */
void bvarith_buffer_sub_mono(bvarith_buffer_t *b, bv_var_t v, uint32_t *a) {
  uint32_t k;
  uint64_t c;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  k = b->width;
  if (bvconst_is_zero(a, k)) return;

  c = a[0]; 
  if (k == 2) {
    c += ((uint64_t) a[1]) << 32;
  }

  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    if (k > 2) {
      bvconst_sub(p->coeff.ptr, k, a);
    } else {
      p->coeff.c -= c;
    }
  } else {
    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->var = v;
    aux->next = p;
    if (k > 2) {
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_negate2(aux->coeff.ptr, k, a);
    } else {
      aux->coeff.c = -c;
    }
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add 1 * v to b
 */
void bvarith_buffer_add_var(bvarith_buffer_t *b, bv_var_t v) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  k = b->width;
  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    if (k > 2) {
      bvconst_add_one(p->coeff.ptr, k);
    } else {
      p->coeff.c ++;
    }
  } else {
    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->var = v;
    aux->next = p;
    if (k > 2) {
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_set_one(aux->coeff.ptr, k);
    } else {
      aux->coeff.c = 1;
    }
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add -1 * v to b
 */
void bvarith_buffer_sub_var(bvarith_buffer_t *b, bv_var_t v) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  k = b->width;
  m = &b->manager->pm;
  p = b->list; // p == start marker (to be skipped)

  do {
    q = p; 
    p = q->next;
  } while (polymanager_var_precedes(m, p->var, v));

  if (p->var == v) {
    if (k > 2) {
      bvconst_sub_one(p->coeff.ptr, k);
    } else {
      p->coeff.c --;
    }
  } else {
    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->var = v;
    aux->next = p;
    if (k > 2) {
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_set_minus_one(aux->coeff.ptr, k);
    } else {
      aux->coeff.c = ((uint64_t) -1);
    }
    q->next = aux;
    b->nterms ++;
  }  
}


/*
 * Add a constant a to b
 */
void bvarith_buffer_add_const(bvarith_buffer_t *b, uint32_t *a) {
  bvarith_buffer_add_mono(b, const_idx, a);
}


/*
 * Subtract a constant a from b
 */
void bvarith_buffer_sub_const(bvarith_buffer_t *b, uint32_t *a) {
  bvarith_buffer_sub_mono(b, const_idx, a);
}



/*
 * Multiply by constant a
 * - should work if a == 0, but the result will not be normalized
 */
void bvarith_buffer_mul_const(bvarith_buffer_t *b, uint32_t *a) {
  uint32_t k;
  bvmlist_t *p;
  uint64_t c;

  k = b->width;
  p = b->list->next;


  if (k <= 2) {
    // store constant in c
    c = a[0];
    if (k == 2) {
      c += ((uint64_t) a[1]) << 32;
    }

    while (p->var < max_idx) {
      p->coeff.c *= c;
      p = p->next;
    }

  } else {
    while (p->var < max_idx) {
      bvconst_mul(p->coeff.ptr, k, a);
      p = p->next;
    }
  }
}



/*
 * Multiply by variable v
 */
void bvarith_buffer_mul_var(bvarith_buffer_t *b, bv_var_t v) {
  bvmlist_t *p;
  bv_var_manager_t *m;
  bv_var_t v1;

  assert(polymanager_var_is_valid(&b->manager->pm, v));

  m = b->manager;
  p = b->list->next;
  v1 = p->var;

  while (v1 < max_idx) {
    p->var = bv_var_manager_mul_var(m, v1, v);
    p = p->next;
    v1 = p->var;
  }
}



/*
 * Add e1 to b. Both must have the same size (and width).
 */
static void wide_buffer_add_expr(bvarith_buffer_t *b, bvarith_expr_t *e1) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmono_t *p1;

  assert(b->width == e1->width && b->width > 2);

  k = b->width;
  m = &b->manager->pm;
  p = b->list;

  p1 = e1->mono;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      bvconst_add(p->coeff.ptr, k, p1->coeff.ptr);
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_set(aux->coeff.ptr, k, p1->coeff.ptr);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 ++;
    v = p1->var;
  }  
}

static void narrow_buffer_add_expr(bvarith_buffer_t *b, bvarith_expr_t *e1) {
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmono_t *p1;

  assert(b->width == e1->width && b->width <= 2);

  m = &b->manager->pm;
  p = b->list;

  p1 = e1->mono;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      p->coeff.c += p1->coeff.c;
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.c = p1->coeff.c;
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 ++;
    v = p1->var;
  }  
}

void bvarith_buffer_add_expr(bvarith_buffer_t *b, bvarith_expr_t *e1) {
  assert(b->size == e1->size);
  if (b->width <= 2) {
    narrow_buffer_add_expr(b, e1);
  } else {
    wide_buffer_add_expr(b, e1);
  }  
}


/*
 * Subtract e1 from b. Both must have the same size (and width).
 */
static void wide_buffer_sub_expr(bvarith_buffer_t *b, bvarith_expr_t *e1) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmono_t *p1;

  assert(b->width == e1->width && b->width > 2);

  k = b->width;
  m = &b->manager->pm;
  p = b->list;

  p1 = e1->mono;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      bvconst_sub(p->coeff.ptr, k, p1->coeff.ptr);
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_negate2(aux->coeff.ptr, k, p1->coeff.ptr);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 ++;
    v = p1->var;
  }  
}

static void narrow_buffer_sub_expr(bvarith_buffer_t *b, bvarith_expr_t *e1) {
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmono_t *p1;

  assert(b->width == e1->width && b->width <= 2);

  m = &b->manager->pm;
  p = b->list;

  p1 = e1->mono;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      p->coeff.c -= p1->coeff.c;
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.c = - p1->coeff.c;
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 ++;
    v = p1->var;
  }  
}

void bvarith_buffer_sub_expr(bvarith_buffer_t *b, bvarith_expr_t *e1) {
  assert(b->size == e1->size);
  if (b->width <= 2) {
    narrow_buffer_sub_expr(b, e1);
  } else {
    wide_buffer_sub_expr(b, e1);
  }  
}



/*
 * Auxiliary functions for multiplication
 */

/*
 * Add a * v1 * e1 to b. a, e1, and b must have the same bit size (and width).
 */
void wide_buffer_add_mono_times_expr(bvarith_buffer_t *b, bvarith_expr_t *e1, bv_var_t v1, uint32_t *a) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  bv_var_manager_t *m;
  polynomial_manager_t *pm;
  bv_var_t v;
  bvmono_t *p1;

  assert(b->width == e1->width && b->width > 2);

  k = b->width;
  m = b->manager;
  pm = &m->pm;
  p = b->list;

  p1 = e1->mono;
  v = p1->var;

  while (v < max_idx) {
    if (v1 != const_idx) v = bv_var_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      bvconst_addmul(p->coeff.ptr, k, p1->coeff.ptr, a);
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.ptr = bvconst_alloc(k);      
      bvconst_mul2(aux->coeff.ptr, k, p1->coeff.ptr, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 ++;
    v = p1->var;
  }  
}

void narrow_buffer_add_mono_times_expr(bvarith_buffer_t *b, bvarith_expr_t *e1, bv_var_t v1, uint64_t a) {
  bvmlist_t *p, *q, *aux;
  bv_var_manager_t *m;
  polynomial_manager_t *pm;
  bv_var_t v;
  bvmono_t *p1;

  assert(b->width == e1->width && b->width <= 2);

  m = b->manager;
  pm = &m->pm;
  p = b->list;

  p1 = e1->mono;
  v = p1->var;

  while (v < max_idx) {
    if (v1 != const_idx) v = bv_var_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      p->coeff.c += a * p1->coeff.c;
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.c = a * p1->coeff.c;
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 ++;
    v = p1->var;
  }  
}


/*
 * Multiply b by e1
 */
void bvarith_buffer_mul_expr(bvarith_buffer_t *b, bvarith_expr_t *e1) {
  uint32_t k;
  bvmlist_t *p, *q, *start;
  bv_var_t v;

  // reset b, keep list of monomials in p
  b->nterms = 0;
  start = b->list;
  p = start->next;

  // new end marker 
  q = (bvmlist_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->var = max_idx;
  q->coeff.c = 0;
  start->next = q;

  q = p;
  v = p->var;
  k = b->width;

  if (k <= 2) {
    while (v < max_idx) {
      narrow_buffer_add_mono_times_expr(b, e1, v, p->coeff.c);
      p = p->next;
      v = p->var;
    }

    // free list q
    while (q != NULL) {
      p = q->next;
      objstore_free(b->store, q);
      q = p;
    }

  } else {

    while (v < max_idx) {
      wide_buffer_add_mono_times_expr(b, e1, v, p->coeff.ptr);
      p = p->next;
      v= p->var;
    }

    // free list q
    while (q->var < max_idx) {
      p = q->next;
      bvconst_free(q->coeff.ptr, k);
      objstore_free(b->store, q);
      q = p;
    }
    // must not call bvconst_free on end marker
    objstore_free(b->store, q);
  }

}





/*
 * Add b1 to b. Both must have the same size (and width).
 */
static void wide_buffer_add_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmlist_t *p1;

  assert(b->width == b1->width && b->width > 2);

  k = b->width;
  m = &b->manager->pm;
  p = b->list;

  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      bvconst_add(p->coeff.ptr, k, p1->coeff.ptr);
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_set(aux->coeff.ptr, k, p1->coeff.ptr);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 = p1->next;
    v = p1->var;
  }  
}

static void narrow_buffer_add_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmlist_t *p1;

  assert(b->width == b1->width && b->width <= 2);

  m = &b->manager->pm;
  p = b->list;

  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      p->coeff.c += p1->coeff.c;
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.c = p1->coeff.c;
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 = p1->next;
    v = p1->var;
  }  
}

void bvarith_buffer_add_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  assert(b->size == b1->size);
  if (b->width <= 2) {
    narrow_buffer_add_buffer(b, b1);
  } else {
    wide_buffer_add_buffer(b, b1);
  }  
}


/*
 * Subtract b1 from b. Both must have the same size (and width).
 */
static void wide_buffer_sub_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmlist_t *p1;

  assert(b->width == b1->width && b->width > 2);

  k = b->width;
  m = &b->manager->pm;
  p = b->list;

  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      bvconst_sub(p->coeff.ptr, k, p1->coeff.ptr);
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.ptr = bvconst_alloc(k);
      bvconst_negate2(aux->coeff.ptr, k, p1->coeff.ptr);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 = p1->next;
    v = p1->var;
  }  
}

static void narrow_buffer_sub_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  bvmlist_t *p, *q, *aux;
  polynomial_manager_t *m;
  bv_var_t v;
  bvmlist_t *p1;

  assert(b->width == b1->width && b->width <= 2);

  m = &b->manager->pm;
  p = b->list;

  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(m, p->var, v));

    if (p->var == v) {
      p->coeff.c -= p1->coeff.c;
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.c = - p1->coeff.c;
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 = p1->next;
    v = p1->var;
  }  
}

void bvarith_buffer_sub_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  assert(b->size == b1->size);
  if (b->width <= 2) {
    narrow_buffer_sub_buffer(b, b1);
  } else {
    wide_buffer_sub_buffer(b, b1);
  }  
}



/*
 * Add a * v1 * b1 to b. a, b1, and b must have the same bit size (and width).
 */
void wide_buffer_add_mono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, bv_var_t v1, uint32_t *a) {
  uint32_t k;
  bvmlist_t *p, *q, *aux;
  bv_var_manager_t *m;
  polynomial_manager_t *pm;
  bv_var_t v;
  bvmlist_t *p1;

  assert(b->width == b1->width && b->width > 2);

  k = b->width;
  m = b->manager;
  pm = &m->pm;
  p = b->list;

  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    if (v1 != const_idx) v = bv_var_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      bvconst_addmul(p->coeff.ptr, k, p1->coeff.ptr, a);
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.ptr = bvconst_alloc(k);      
      bvconst_mul2(aux->coeff.ptr, k, p1->coeff.ptr, a);
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 = p1->next;
    v = p1->var;
  }  
}

void narrow_buffer_add_mono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, bv_var_t v1, uint64_t a) {
  bvmlist_t *p, *q, *aux;
  bv_var_manager_t *m;
  polynomial_manager_t *pm;
  bv_var_t v;
  bvmlist_t *p1;

  assert(b->width == b1->width && b->width <= 2);

  m = b->manager;
  pm = &m->pm;
  p = b->list;

  p1 = b1->list->next;
  v = p1->var;

  while (v < max_idx) {
    if (v1 != const_idx) v = bv_var_manager_mul_var(m, v, v1);

    do {
      q = p;
      p = q->next;
    } while (polymanager_var_precedes(pm, p->var, v));

    if (p->var == v) {
      p->coeff.c += a * p1->coeff.c;
    } else {
      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->var = v;
      aux->next = p;
      aux->coeff.c = a * p1->coeff.c;
      p = aux;
      q->next = aux;
      b->nterms ++;
    }

    p1 = p1->next;
    v = p1->var;
  }  
}



/*
 * Multiply b by b1. Both must have the same size.
 */
void bvarith_buffer_mul_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  uint32_t k;
  bvmlist_t *p, *q, *start;
  bv_var_t v;

  assert(b != b1);

  // reset b, keep list of monomials in p
  b->nterms = 0;
  start = b->list;
  p = start->next;

  // new end marker 
  q = (bvmlist_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->var = max_idx;
  q->coeff.c = 0;
  start->next = q;

  q = p;
  v = p->var;
  k = b->width;

  if (k <= 2) {
    while (v < max_idx) {
      narrow_buffer_add_mono_times_buffer(b, b1, v, p->coeff.c);
      p = p->next;
      v = p->var;
    }

    // free list q
    while (q != NULL) {
      p = q->next;
      objstore_free(b->store, q);
      q = p;
    }

  } else {

    while (v < max_idx) {
      wide_buffer_add_mono_times_buffer(b, b1, v, p->coeff.ptr);
      p = p->next;
      v = p->var;
    }

    // free list q
    while (q->var < max_idx) {
      p = q->next;
      bvconst_free(q->coeff.ptr, k);
      objstore_free(b->store, q);
      q = p;
    }
    // must not call bvconst_free on end marker
    objstore_free(b->store, q);

  }

}


/*
 * Square of b
 */
void bvarith_buffer_square(bvarith_buffer_t *b) {
  bvarith_buffer_t aux;
  bvmlist_t *start;

  /*
   * make a shallow copy of b into aux then call mul
   * for this to work, we must make sure that the first
   * element of aux->list is a copy of the first element of 
   * b->list
   */
  aux = *b;

  start = (bvmlist_t *) objstore_alloc(aux.store);
  start->var = null_idx;
  start->next = aux.list->next;
  start->coeff.c = 0;
  aux.list = start;

  bvarith_buffer_mul_buffer(b, &aux);

  // cleanup: delete start
  objstore_free(aux.store, start);
}
