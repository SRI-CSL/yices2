/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BUFFERS FOR OPERATIONS ON BIT-VECTOR POLYNOMIALS
 */

/*
 * Bitvector polynomials are sums of pairs <coeff, pp>
 * - the coeff is a bitvector constant
 * - pp is a power product (cf. power_products.h)
 * - all coefficients have the same bit-size
 * - the data structure in this module support arbitrary
 *   bit size; coefficients are pointers to 32bit words
 *   (cf. bv_constants.h).
 *
 * In normal form, polynomials have the following properties:
 * - the coefficients are all reduced modulo 2^n
 *   and are all non zero
 * - the monomials are stored in deg-lex order: lower degree
 *   monomials appear first; monomials of equal degree are
 *   sorted in lexicographic order.
 */

#include "terms/bvarith_buffers.h"
#include "utils/hash_functions.h"

#include "yices_limits.h"



/***********************
 * BUFFER  OPERATIONS  *
 **********************/

/*
 * Initialize store s for list elements
 */
void init_bvmlist_store(object_store_t *s) {
  init_objstore(s, sizeof(bvmlist_t), BVMLIST_BANK_SIZE);
}


/*
 * Delete store s: this must not be called before all
 * buffers that refer to s are deleted.
 */
void delete_bvmlist_store(object_store_t *s) {
  delete_objstore(s);
}



/*
 * Initialize buffer b to the zero polynomial
 * - ptbl = attached power product table
 * - s = attached store
 * Build the end marker
 */
void init_bvarith_buffer(bvarith_buffer_t *b, pprod_table_t *ptbl, object_store_t *s) {
  bvmlist_t *end;

  b->nterms = 0;
  b->bitsize = 0;
  b->width = 0;
  b->store = s;
  b->ptbl = ptbl;

  end = (bvmlist_t *) objstore_alloc(s);
  end->next = NULL;
  end->coeff = NULL;
  end->prod = end_pp;

  b->list = end;
}


/*
 * Clear b:
 * - free all coefficients.
 * - empty the list (but keep the end marker).
 * - leave bitsize and width unchanged
 */
static void bvarith_buffer_clear(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;
  uint32_t k;

  if (b->nterms == 0) return;

  k = b->width;
  p = b->list;
  q = p->next;
  while (q != NULL) {
    assert(p->prod != end_pp);
    bvconst_free(p->coeff, k);
    objstore_free(b->store, p);
    p = q;
    q = p->next;
  }

  assert(p->prod == end_pp);
  b->list = p;
  b->nterms = 0;
}


/*
 * Delete b and free all attached memory
 */
void delete_bvarith_buffer(bvarith_buffer_t *b) {
  bvarith_buffer_clear(b);
  assert(b->list->prod == end_pp);
  objstore_free(b->store, b->list);

  b->store = NULL;
  b->ptbl = NULL;
  b->list = NULL;
}


/*
 * Prepare buffer b: clear b then set bit size equal to n
 * - n must be positive and no more than YICES_MAX_BVSIZE
 */
void bvarith_buffer_prepare(bvarith_buffer_t *b, uint32_t n) {
  uint32_t w;

  assert(0 < n && n <= YICES_MAX_BVSIZE);

  if (b->bitsize != 0) {
    bvarith_buffer_clear(b);
  }

  w = (n + 31) >> 5;
  b->bitsize = n;
  b->width = w;
}




/*
 * Normalize the coefficients modulo 2^n (set high-order bits to 0)
 * remove the zero monomials from b
 */
void bvarith_buffer_normalize(bvarith_buffer_t *b) {
  bvmlist_t *p;
  bvmlist_t **q;
  uint32_t n, k;

  n = b->bitsize;
  k = b->width;
  q = &b->list;
  p = *q;
  assert(p == b->list);

  while (p->next != NULL) {
    assert(p == *q && p->prod != end_pp);
    bvconst_normalize(p->coeff, n);
    if (bvconst_is_zero(p->coeff, k)) {
      // remove p
      *q = p->next;
      bvconst_free(p->coeff, k);
      objstore_free(b->store, p);
      b->nterms --;
    } else {
      q = &p->next;
    }
    p = *q;
  }
}



/*
 * QUERIES
 */

/*
 * Check whether b is constant
 * - b must be normalized
 */
bool bvarith_buffer_is_constant(bvarith_buffer_t *b) {
  return b->nterms == 0 || (b->nterms == 1 && b->list->prod == empty_pp);
}


/*
 * Read the constant term of b as a 64bit integer.
 * - b's bitsize must be between 1 and 64
 * - b must be normalized
 */
uint64_t bvarith_buffer_get_constant64(bvarith_buffer_t *b) {
  bvmlist_t *p;
  uint64_t c;

  assert(0 < b->bitsize && b->bitsize <= 64);

  c = 0;
  p = b->list;
  if (p->prod == empty_pp) {
    // constant term
    if (b->width == 1) {
      c = bvconst_get32(p->coeff);
    } else {
      assert(b->width == 2);
      c = bvconst_get64(p->coeff);
    }
  }

  return c;
}


/*
 * Copy constant stored in b into c
 * - b must be normalized
 * - the returned constant has bitsize equal to b->bitsize
 */
void bvarith_buffer_copy_constant(bvarith_buffer_t *b, bvconstant_t *c) {
  bvmlist_t *p;

  assert(b->bitsize > 0);

  bvconstant_set_bitsize(c, b->bitsize);
  p = b->list;
  if (p->prod == empty_pp) {
    // p is the constant monomial
    bvconst_set(c->data, b->width, p->coeff);
  } else {
    // constant term is zero
    bvconst_clear(c->data, b->width);
  }
}



/*
 * Main monomial = monomial whose pp is the main term
 * - b must be normalized and non zero
 * - this returns the last element in b's monomial list
 */
bvmlist_t *bvarith_buffer_main_mono(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;

  assert(b->nterms > 0);

  p = b->list;
  q = p->next;
  while (q->next != NULL) {
    p = q;
    q = q->next;
  }

  assert(p->prod != end_pp && p->next != NULL && p->next->prod == end_pp);

  return p;
}


/*
 * Get degree of polynomial in buffer b.
 * - b must be normalized
 * - returns 0 if b is zero
 */
uint32_t bvarith_buffer_degree(bvarith_buffer_t *b) {
  bvmlist_t *p;

  if (b->nterms == 0) {
    return 0;
  }

  p = bvarith_buffer_main_mono(b);
  return pprod_degree(p->prod);
}



/*
 * Main term = maximal power product of b in the deg-lex ordering.
 * - b must be normalized and non zero
 */
pprod_t *bvarith_buffer_main_term(bvarith_buffer_t *b) {
  bvmlist_t *p;

  p = bvarith_buffer_main_mono(b);
  return p->prod;
}


/*
 * Check whether b1 and b2 are equal
 * - both must be normalized and use the same ptbl
 */
bool bvarith_buffer_equal(bvarith_buffer_t *b1, bvarith_buffer_t *b2) {
  bvmlist_t *p1, *p2;
  uint32_t k;

  assert(b1->ptbl == b2->ptbl);

  if (b1->nterms != b2->nterms || b1->bitsize != b2->bitsize) {
    return false;
  }

  k = b1->width;
  p1 = b1->list;
  p2 = b2->list;

  while (p1->prod == p2->prod) {
    if (p1->prod == end_pp) return true;
    if (bvconst_neq(p1->coeff, p2->coeff, k)) return false;
    p1 = p1->next;
    p2 = p2->next;
  }

  return false;
}



/******************************
 *  POLYNOMIAL CONSTRUCTION   *
 *****************************/

/*
 * All operations update the first argument b.
 * They do not ensure that b is normalized.
 *
 * Some operations have a power product r as argument.
 * The power product r must be defined in b's internal
 * power-product table: either r is empty_pp, or r is
 * a tagged variable, or r occurs in b->ptbl.
 *
 * Some operations use another buffer b1. In such cases,
 * b and b1 must have the same power-product table.
 * Unless otherwise indicated, the operations work correctly
 * if b1 is equal to b (but this use is not recommended).
 */

/*
 * Assign the constant 1 to b
 */
void bvarith_buffer_set_one(bvarith_buffer_t *b) {
  bvmlist_t *p;
  uint32_t k;

  assert(b->bitsize > 0);

  if (b->nterms > 0) {
    bvarith_buffer_clear(b);
  }

  assert(b->nterms == 0 && b->list->prod == end_pp);

  k = b->width;

  // new monomial
  p = (bvmlist_t *) objstore_alloc(b->store);
  p->next = b->list;
  p->prod = empty_pp;
  p->coeff = bvconst_alloc(k);
  bvconst_set_one(p->coeff, k);

  // insert p in the list
  b->list = p;
  b->nterms = 1;
}


/*
 * Assign the constant -1 to b
 */
void bvarith_buffer_set_minus_one(bvarith_buffer_t *b) {
  bvmlist_t *p;
  uint32_t k;

  assert(b->bitsize > 0);

  if (b->nterms > 0) {
    bvarith_buffer_clear(b);
  }

  assert(b->nterms == 0 && b->list->prod == end_pp);

  k = b->width;

  // new monomial
  p = (bvmlist_t *) objstore_alloc(b->store);
  p->next = b->list;
  p->prod = empty_pp;
  p->coeff = bvconst_alloc(k);
  bvconst_set_minus_one(p->coeff, k);

  // insert p in the list
  b->list = p;
  b->nterms = 1;
}




/*
 * Multiply b by -1
 */
void bvarith_buffer_negate(bvarith_buffer_t *b) {
  bvmlist_t *p;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  p = b->list;
  while (p->next != NULL) {
    bvconst_negate(p->coeff, k);
    p = p->next;
  }
}


/*
 * Multiply b by constant a
 */
void bvarith_buffer_mul_const(bvarith_buffer_t *b, uint32_t *a) {
  bvmlist_t *p;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  p = b->list;
  while (p->next != NULL) {
    bvconst_mul(p->coeff, k, a);
    p = p->next;
  }
}


/*
 * Multiply b by power product r
 */
void bvarith_buffer_mul_pp(bvarith_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  bvmlist_t *p;

  assert(b->bitsize > 0);

  /*
   * We use the fact that the monomial ordering
   * is compatible with multiplication, that is
   *    r1 < r2 => r * r1 < r * r2
   */
  tbl = b->ptbl;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    p->prod = pprod_mul(tbl, p->prod, r);
    p = p->next;
  }
}


/*
 * Multiply b by (- r)
 */
void bvarith_buffer_mul_negpp(bvarith_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  bvmlist_t *p;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  tbl = b->ptbl;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    p->prod = pprod_mul(tbl, p->prod, r);
    bvconst_negate(p->coeff, k);
    p = p->next;
  }
}


/*
 * Multiply b by a * r
 */
void bvarith_buffer_mul_mono(bvarith_buffer_t *b, uint32_t *a, pprod_t *r) {
  pprod_table_t *tbl;
  bvmlist_t *p;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  tbl = b->ptbl;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    p->prod = pprod_mul(tbl, p->prod, r);
    bvconst_mul(p->coeff, k, a);
    p = p->next;
  }

}



/*
 * Add a * r to b
 */
void bvarith_buffer_add_mono(bvarith_buffer_t *b, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  if (bvconst_is_zero(a, k)) return;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is the predecessor of p
  if (p->prod == r) {
    bvconst_add(p->coeff, k, a);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = bvconst_alloc(k);
    bvconst_set(aux->coeff, k, a);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add -a * r to b
 */
void bvarith_buffer_sub_mono(bvarith_buffer_t *b, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  if (bvconst_is_zero(a, k)) return;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is the predecessor of p
  if (p->prod == r) {
    bvconst_sub(p->coeff, k, a);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = bvconst_alloc(k);
    bvconst_negate2(aux->coeff, k, a);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}



/*
 * Add constant a to b
 */
void bvarith_buffer_add_const(bvarith_buffer_t *b, uint32_t *a) {
  bvarith_buffer_add_mono(b, a, empty_pp);
}


/*
 * Subtract constant from b
 */
void bvarith_buffer_sub_const(bvarith_buffer_t *b, uint32_t *a) {
  bvarith_buffer_sub_mono(b, a, empty_pp);
}



/*
 * Add a * c * r to b
 */
void bvarith_buffer_add_const_times_mono(bvarith_buffer_t *b, uint32_t *a, uint32_t *c, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  if (bvconst_is_zero(a, k) || bvconst_is_zero(c, k)) return;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is the predecessor of p
  if (p->prod == r) {
    bvconst_addmul(p->coeff, k, a, c);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = bvconst_alloc(k);
    bvconst_mul2(aux->coeff, k, a, c);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }

}


/*
 * Add -a * c * r to b
 */
void bvarith_buffer_sub_const_times_mono(bvarith_buffer_t *b, uint32_t *a, uint32_t *c, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  if (bvconst_is_zero(a, k) || bvconst_is_zero(c, k)) return;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is the predecessor of p
  if (p->prod == r) {
    bvconst_submul(p->coeff, k, a, c);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = bvconst_alloc(k);
    bvconst_clear(aux->coeff, k);
    bvconst_submul(aux->coeff, k, a, c);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add a * c to b
 */
void bvarith_buffer_add_const_times_const(bvarith_buffer_t *b, uint32_t *a, uint32_t *c) {
  bvarith_buffer_add_const_times_mono(b, a, c, empty_pp);
}


/*
 * Subtract a * c to b
 */
void bvarith_buffer_sub_const_times_const(bvarith_buffer_t *b, uint32_t *a, uint32_t *c) {
  bvarith_buffer_sub_const_times_mono(b, a, c, empty_pp);
}




/*
 * Add r to b
 */
void bvarith_buffer_add_pp(bvarith_buffer_t *b, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is the predecessor of p
  if (p->prod == r) {
    bvconst_add_one(p->coeff, k);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = bvconst_alloc(k);
    bvconst_set_one(aux->coeff, k);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add -r to b
 */
void bvarith_buffer_sub_pp(bvarith_buffer_t *b, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is the predecessor of p
  if (p->prod == r) {
    bvconst_sub_one(p->coeff, k);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = bvconst_alloc(k);
    bvconst_set_minus_one(aux->coeff, k);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add p1 to b
 */
void bvarith_buffer_add_mlist(bvarith_buffer_t *b, bvmlist_t *p1) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_add(p->coeff, k, p1->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_set(aux->coeff, k, p1->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add (-p1) to b
 */
void bvarith_buffer_sub_mlist(bvarith_buffer_t *b, bvmlist_t *p1) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_sub(p->coeff, k, p1->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_negate2(aux->coeff, k, p1->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}



/*
 * Add a * p1 to b
 */
void bvarith_buffer_add_const_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_addmul(p->coeff, k, p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_mul2(aux->coeff, k, p1->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add (-a) * p1 to b
 */
void bvarith_buffer_sub_const_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_submul(p->coeff, k, p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_clear(aux->coeff, k);
      bvconst_submul(aux->coeff, k, p1->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add r * p1 to b
 */
void bvarith_buffer_add_pp_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_add(p->coeff, k, p1->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_set(aux->coeff, k, p1->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }

}


/*
 * Add - r * p1 to b
 */
void bvarith_buffer_sub_pp_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_sub(p->coeff, k, p1->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_negate2(aux->coeff, k, p1->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add a * r * p1 to b
 */
void bvarith_buffer_add_mono_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_addmul(p->coeff, k, p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_mul2(aux->coeff, k, p1->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}

/*
 * Add -a * r * p1 to b
 */
void bvarith_buffer_sub_mono_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      bvconst_submul(p->coeff, k, p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_clear(aux->coeff, k);
      bvconst_submul(aux->coeff, k, p1->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Multiply b by p1
 */
void bvarith_buffer_mul_mlist(bvarith_buffer_t *b, bvmlist_t *p1) {
  bvmlist_t *p, *q;
  uint32_t k;

  // keep b's current list of monomials in p
  p = b->list;

  // reset b to the zero polynomial
  q = (bvmlist_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->coeff = NULL;
  q->prod = end_pp;

  b->nterms = 0;
  b->list = q;

  // keep a copy of p in q to cleanup when we're done
  q = p;

  // the constant term of p is first (if any)
  if (p->prod == empty_pp) {
    bvarith_buffer_add_const_times_mlist(b, p1, p->coeff);
    p = p->next;
  }

  // other monomials of p
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    bvarith_buffer_add_mono_times_mlist(b, p1, p->coeff, p->prod);
    p = p->next;
  }

  // cleanup: free list q
  k = b->width;
  while (q->next != NULL) {
    p = q->next;
    bvconst_free(q->coeff, k);
    objstore_free(b->store, q);
    q = p;
  }

  // delete the end marker
  assert(q->prod == end_pp);
  objstore_free(b->store, q);
}


/*
 * Compute the square of b
 */
void bvarith_buffer_square(bvarith_buffer_t *b) {
  bvarith_buffer_mul_mlist(b, b->list);
}



/*
 * Add p1 * p2 to b
 */
void bvarith_buffer_add_mlist_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, bvmlist_t *p2) {
  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    bvarith_buffer_add_const_times_mlist(b, p2, p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    bvarith_buffer_add_mono_times_mlist(b, p2, p1->coeff, p1->prod);
    p1 = p1->next;
  }
}


/*
 * Add - p1 * p2 to b
 */
void bvarith_buffer_sub_mlist_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, bvmlist_t *p2) {
  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    bvarith_buffer_sub_const_times_mlist(b, p2, p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    bvarith_buffer_sub_mono_times_mlist(b, p2, p1->coeff, p1->prod);
    p1 = p1->next;
  }
}



/*
 * Multiply b by p1 ^ d
 * - use aux as an auxiliary buffer.
 * - aux must be distinct from b, but use the same power_product table
 */
void bvarith_buffer_mul_mlist_power(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t d, bvarith_buffer_t *aux) {
  uint32_t i;

  assert(b != aux && aux->ptbl == b->ptbl);

  if (d <= 4) {
    // small exponent: don't use aux
    for (i=0; i<d; i++) {
      bvarith_buffer_mul_mlist(b, p1);
      bvarith_buffer_normalize(b);
    }
  } else {
    // larger exponent
    bvarith_buffer_prepare(aux, b->bitsize);
    bvarith_buffer_add_mlist(aux, p1); // aux := p1
    for (;;) {
      /*
       * loop invariant: b0 * p1^d0 == b * aux^d
       * with b0 = b on entry to the function
       *      d0 = d on entry to the function
       */
      assert(d > 0);
      if ((d & 1) != 0) {
        bvarith_buffer_mul_mlist(b, aux->list); // b := b * aux
        bvarith_buffer_normalize(b);
      }
      d >>= 1;                             // d := d/2
      if (d == 0) break;
      bvarith_buffer_square(aux);          // aux := aux^2
      bvarith_buffer_normalize(aux);
    }
  }
}


/*
 * Extract the content of b as a list of monomials, then reset b to the zero polynomial
 * - b must be normalized
 */
bvmlist_t *bvarith_buffer_get_mlist(bvarith_buffer_t *b) {
  bvmlist_t *r, *q;

  r = b->list;

  // reset b to the end-marker only
  q = (bvmlist_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->coeff = NULL;
  q->prod = end_pp;

  b->list = q;
  b->nterms = 0;

  return r;
}


/*
 * Hash code for a monomial list p
 * - n = bitsize of p
 * - power products are hash-consed in pprod_table so it's enough to
 *   compute the hash code of the pointer
 */
uint32_t hash_bvmlist(bvmlist_t *p, uint32_t n) {
  uint32_t h, k, l;

  k = (n + 31) >> 5; // width
  h = HASH_BVPOLY_SEED + n;
  while (p->next != NULL) {
    h = jenkins_hash_array(p->coeff, k, h); // coefficient
    l = jenkins_hash_ptr(p->prod);   // power product
    h = jenkins_hash_mix3(l, n, h);

    p = p->next;
  }

  return h;
}


/*
 * Test whether p1 and p2 are equal
 * - both lists must be sorted, and terminated by the end marker,
 *   and use the same pprod table.
 * - n = bitsize of both p1 and p2
 */
bool equal_bvmlists(bvmlist_t *p1, bvmlist_t *p2, uint32_t n) {
  uint32_t k;

  k = (n + 31) >> 5;
  while (p1->prod == p2->prod) {
    if (p1->prod == end_pp) return true; // end marker
    if (bvconst_neq(p1->coeff, p2->coeff, k)) return false;
    p1 = p1->next;
    p2 = p2->next;
  }

  return false;
}


/*
 * Delete all monomials in *p
 * - store = the relevant monomial store (all monomials of p
 *   must have been allocated in store).
 * - n = number of bits in *p
 */
void free_bvmlist(bvmlist_t *p, object_store_t *store, uint32_t n) {
  bvmlist_t *q;
  uint32_t k;

  k = (n + 31) >> 5;
  q = p->next;
  while (q != NULL) {
    assert(p->prod != end_pp);
    bvconst_free(p->coeff, k);
    objstore_free(store, p);
    p = q;
    q = p->next;
  }

  assert(p->prod == end_pp && p->coeff == NULL);
  objstore_free(store, p);
}



/*******************************************
 *  OPERATIONS WITH POLYNOMIAL STRUCTURES  *
 ******************************************/

/*
 * All operations below take three arguments:
 * - b is an arithmetic buffer
 * - poly is an array of monomials
 * - pp is an array of power products
 *   if poly[i] is a monomial a_i x_i then pp[i] must be the conversion
 *   of x_i to a power product.
 * - poly must be terminated by and end-marker (var = max_idx).
 * - pp must be sorted in the deg-lex ordering and have at least
 *   as many elements as length of mono - 1.
 */


#ifndef NDEBUG

/*
 * For debugging: check that q contains valid power products
 * sorted in increasing deg-lex ordering.
 */
static bool good_pprod_array(bvmono_t *poly, pprod_t **pp) {
  pprod_t *r;

  if (poly->var < max_idx) {
    r = *pp;
    poly ++;
    pp ++;
    while (poly->var < max_idx) {
      if (! pprod_precedes(r, *pp)) return false;
      r = *pp;
      pp ++;
      poly ++;
    }
  }

  return true;
}

#endif


/*
 * Add poly to buffer b
 */
void bvarith_buffer_add_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  bvmono_t *m;
  pprod_t *r1;
  uint32_t k;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  k = b->width;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m points to a pair (coeff, x_i)
    // r1 = power product for x_i
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      bvconst_add(p->coeff, k, m->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_set(aux->coeff, k, m->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial
    m ++;
    pp ++;
  }
}


 /*
 * Subtract poly from buffer b
 */
void bvarith_buffer_sub_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  bvmono_t *m;
  pprod_t *r1;
  uint32_t k;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  k = b->width;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m points to a pair (coeff, x_i)
    // r1 = power product for x_i
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      bvconst_sub(p->coeff, k, m->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_negate2(aux->coeff, k, m->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    m ++;
    pp ++;
  }
}


/*
 * Add a * poly to buffer b
 */
void bvarith_buffer_add_const_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  bvmono_t *m;
  pprod_t *r1;
  uint32_t k;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  k = b->width;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m points to a pair (coeff, x_i)
    // r1 = power product for x_i
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      bvconst_addmul(p->coeff, k, m->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_mul2(aux->coeff, k, m->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;

      b->nterms ++;
    }

    // move to the next monomial
    m ++;
    pp ++;
  }
}


/*
 * Subtract a * poly from b
 */
void bvarith_buffer_sub_const_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  bvmono_t *m;
  pprod_t *r1;
  uint32_t k;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  k = b->width;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m points to a pair (coeff, x_i)
    // r1 = power product for x_i
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      bvconst_submul(p->coeff, k, m->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_clear(aux->coeff, k);
      bvconst_submul(aux->coeff, k, m->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;

      b->nterms ++;
    }

    // move to the next monomial
    m ++;
    pp ++;
  }
}


/*
 * Add a * r * poly to b
 */
void bvarith_buffer_add_mono_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  bvmono_t *m;
  pprod_t *r1;
  uint32_t k;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  k = b->width;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m points to a pair (coeff, x_i)
    // r1 = r * power product for x_i
    r1 = pprod_mul(b->ptbl, *pp, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      bvconst_addmul(p->coeff, k, m->coeff, a);
      q = &b->list;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_mul2(aux->coeff, k, m->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial
    m ++;
    pp ++;
  }
}


/*
 * Add -a * r * poly to b
 */
void bvarith_buffer_sub_mono_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *aux;
  bvmlist_t **q;
  bvmono_t *m;
  pprod_t *r1;
  uint32_t k;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  k = b->width;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m points to a pair (coeff, x_i)
    // r1 = r * power product for x_i
    r1 = pprod_mul(b->ptbl, *pp, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      bvconst_submul(p->coeff, k, m->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_clear(aux->coeff, k);
      bvconst_submul(aux->coeff, k, m->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial
    m ++;
    pp ++;
  }
}


/*
 * Multiply b by poly
 */
void bvarith_buffer_mul_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp) {
  bvmlist_t *p, *q;
  uint32_t k;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  // keep b's current list of monomials in p
  p = b->list;

  // reset b to the zero polynomial
  q = (bvmlist_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->prod = end_pp;
  b->nterms = 0;
  b->list = q;

  // keep a copy of p in q to cleanup when we're done
  q = p;

  // the constant term of p is first (if any)
  if (p->prod == empty_pp) {
    bvarith_buffer_add_const_times_bvpoly(b, poly, pp, p->coeff);
    p = p->next;
  }

  // other monomials of p
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    bvarith_buffer_add_mono_times_bvpoly(b, poly, pp, p->coeff, p->prod);
    p = p->next;
  }

  // cleanup: free list q
  k = b->width;
  while (q->next != NULL) {
    p = q->next;
    bvconst_free(q->coeff, k);
    objstore_free(b->store, q);
    q = p;
  }

  // delete the end marker
  assert(q->prod == end_pp);
  objstore_free(b->store, q);
}


/*
 * Multiply b by  p ^ d
 * - pp = power products for the variables of p
 * - use aux as an auxiliary buffer
 * - store the result in b (normalized)
 */
void bvarith_buffer_mul_bvpoly_power(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t d, bvarith_buffer_t *aux) {
  uint32_t i;

  assert(aux != b && good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  if (d <= 4) {
    // small exponent: aux is not used
    for (i=0; i<d; i++) {
      bvarith_buffer_mul_bvpoly(b, poly, pp);
      bvarith_buffer_normalize(b);
    }
  } else {
    // larger exponent
    bvarith_buffer_prepare(aux, b->bitsize);
    bvarith_buffer_add_bvpoly(aux, poly, pp); // aux := p
    for (;;) {
      /*
       * loop invariant: b0 * p^d0 == b * aux^ d
       * with b0 = b on entry to the function
       *      d0 = d on entry to the function
       */
      assert(d > 0);
      if ((d & 1) != 0) {
        bvarith_buffer_mul_buffer(b, aux); // b := b * aux
        bvarith_buffer_normalize(b);
      }
      d >>= 1;                           // d := d/2
      if (d == 0) break;
      bvarith_buffer_square(aux);        // aux := aux^2
      bvarith_buffer_normalize(aux);
    }
  }
}



/*******************************************************************
 *  SUPPORT FOR HASH CONSING AND CONVERSION TO POLYNOMIAL OBJECTS  *
 ******************************************************************/

/*
 * The conversion of a buffer b to a polynomial object requires two steps:
 * 1) convert all the power-products in b to integer indices.
 *    This must map empty_pp to const_idx and end_pp to max_idx.
 * 2) build a polynomial from the coefficients of b and the integer indices
 *
 * The operations below use a buffer b and an integer array v.
 * The array v stores the conversion from power-products to integer indices:
 * If b contains a_0 r_0 + ... + a_n r_n then v must have (n+1) elements
 * and the integer  index for power product r_i is v[i].
 *
 * The pair (b, v) defines then a bitvector polynomial
 * P(b, v) = a_1 v[1] + ... + a_n v[n],
 */

/*
 * Hash code for P(b, v).
 * This function is consistent with hash_bvpoly defined in bv_polynomials.c.
 * If P(b, v) = p0 then hash_bvarith_buffer(b, v) = hash_bvpolynomial(p0).
 */
uint32_t hash_bvarith_buffer(bvarith_buffer_t *b, int32_t *v) {
  bvmlist_t *q;
  uint32_t h, k, n;

  h = HASH_BVPOLY_SEED + b->nterms;
  k = b->width;
  n = b->bitsize;
  q = b->list;
  while (q->next != NULL) {
    // coeff in q, variable in v
    h = jenkins_hash_array(q->coeff, k, h);
    h = jenkins_hash_mix3(*v, n, h);

    q = q->next;
    v ++;
  }

  return h;
}



/*
 * Check where P(b, v) is equal to p
 */
bool bvarith_buffer_equal_bvpoly(bvarith_buffer_t *b, int32_t *v, bvpoly_t *p) {
  bvmlist_t *q;
  bvmono_t *mono;
  uint32_t k;
  int32_t x1, x2;

  if (b->nterms == p->nterms && b->bitsize == p->bitsize) {
    k = b->width;
    q = b->list;
    mono = p->mono;
    x1 = *v;
    x2 = mono->var;
    while (x1 == x2) {
      if (x1 == max_idx) return true;
      if (bvconst_neq(q->coeff, mono->coeff, k)) return false;

      mono ++;
      v ++;
      q = q->next;
      x1 = *v;
      x2 = mono->var;
    }
  }

  return false;
}


/*
 * Build P(b, v) (i.e., convert b to a polynomial then reset b).
 * SIDE EFFECT: b is reset to the zero polynomial.
 */
bvpoly_t *bvarith_buffer_get_bvpoly(bvarith_buffer_t *b, int32_t *v) {
  bvpoly_t *tmp;
  bvmlist_t *q, *next;
  uint32_t i, n;

  n = b->nterms;
  tmp = alloc_bvpoly(n, b->bitsize);

  q = b->list;
  for (i=0; i<n; i++) {
    assert(q->prod != end_pp && v[i] < max_idx);
    // we copy q->coeff into mono[i].coeff directly
    tmp->mono[i].var = v[i];
    tmp->mono[i].coeff = q->coeff;
    // free q
    next = q->next;
    objstore_free(b->store, q);
    q = next;
  }

  // empty the buffer: q should be the end marker here
  assert(q->prod == end_pp && q->next == NULL);
  b->list = q;
  b->nterms = 0;

  assert(tmp->mono[n].var == max_idx);

  return tmp;
}
