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

#include <stdint.h>
#include <assert.h>

#include "bvarith_buffers.h"




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
 */
void bvarith_buffer_prepare(bvarith_buffer_t *b, uint32_t n) {
  uint32_t w;

  assert(n > 0);
  if (b->bitsize != 0) {
    bvarith_buffer_clear(b);
  }

  w = (n + 31) >> 5;
  b->bitsize = n;
  b->width = w;
}




/*
 * Fake start element: return a pointer l such
 * that l->next is b->list.
 */
static inline bvmlist_t *fake_start(bvarith_buffer_t *b) {
  bvmlist_t *l;

  l = ((bvmlist_t *) &b->list);
  assert(&l->next == &b->list);
  return l;
}


/*
 * Normalize the coefficients modulo 2^n (set high-order bits to 0)
 * remove the zero monomials from b
 */
void bvarith_buffer_normalize(bvarith_buffer_t *b) {
  bvmlist_t *p, *q;
  uint32_t n, k;

  n = b->bitsize;
  k = b->width;
  q = fake_start(b);
  p = q->next;
  assert(p == b->list);

  while (p->next != NULL) {
    // p == q->next and p is not the end marker
    assert(p == q->next && p->prod != end_pp);
    bvconst_normalize(p->coeff, n);
    if (bvconst_is_zero(p->coeff, k)) {
      // remove p
      q->next = p->next;
      bvconst_free(p->coeff, k);
      objstore_free(b->store, p);
      b->nterms --;
    } else {
      q = p;
    }
    p = q->next;
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
  bvmlist_t *p, *q, *aux;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  if (bvconst_is_zero(a, k)) return;

  q = fake_start(b);
  p = q->next;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = p;
    p = p->next;
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

    q->next = aux;
    b->nterms ++;
  }
}


/*
 * Add -a * r to b
 */
void bvarith_buffer_sub_mono(bvarith_buffer_t *b, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *q, *aux;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;
  if (bvconst_is_zero(a, k)) return;

  q = fake_start(b);
  p = q->next;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = p;
    p = p->next;
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

    q->next = aux;
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
 * Add r to b
 */
void bvarith_buffer_add_pp(bvarith_buffer_t *b, pprod_t *r) {
  bvmlist_t *p, *q, *aux;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;

  q = fake_start(b);
  p = q->next;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = p;
    p = p->next;
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

    q->next = aux;
    b->nterms ++;
  }
}


/*
 * Add -r to b
 */
void bvarith_buffer_sub_pp(bvarith_buffer_t *b, pprod_t *r) {
  bvmlist_t *p, *q, *aux;
  uint32_t k;

  assert(b->bitsize > 0);

  k = b->width;

  q = fake_start(b);
  p = q->next;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = p;
    p = p->next;
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

    q->next = aux;
    b->nterms ++;
  }
}


/*
 * Add b1 to b
 */
void bvarith_buffer_add_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_add(p->coeff, k, p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_set(aux->coeff, k, p1->coeff);
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }
}


/*
 * Add (-b1) to b
 */
void bvarith_buffer_sub_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_sub(p->coeff, k, p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_negate2(aux->coeff, k, p1->coeff);
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }
}



/*
 * Add a * b1 to b
 */
void bvarith_buffer_add_const_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_addmul(p->coeff, k, p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_mul2(aux->coeff, k, p1->coeff, a); 
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }
}


/*
 * Add (-a) * b1 to b
 */
void bvarith_buffer_sub_const_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_submul(p->coeff, k, p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_clear(aux->coeff, k);
      bvconst_submul(aux->coeff, k, p1->coeff, a); 
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }
}


/*
 * Add r * b1 to b
 */
void bvarith_buffer_add_pp_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, pprod_t *r) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_add(p->coeff, k, p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_set(aux->coeff, k, p1->coeff); 
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }

}


/*
 * Add - r * b1 to b
 */
void bvarith_buffer_sub_pp_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, pprod_t *r) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_sub(p->coeff, k, p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_negate2(aux->coeff, k, p1->coeff); 
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }
}


/*
 * Add a * r * b1 to b
 */
void bvarith_buffer_add_mono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_addmul(p->coeff, k, p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_mul2(aux->coeff, k, p1->coeff, a);
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }
}

/*
 * Add -a * r * b1 to b
 */
void bvarith_buffer_sub_mono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a, pprod_t *r) {
  bvmlist_t *p, *q, *aux, *p1;
  pprod_t *r1;
  uint32_t k;

  assert(b->bitsize > 0 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

  k = b->width;
  q = fake_start(b);
  p = q->next;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = p;
      p = p->next;
    }

    if (p->prod == r1) {
      bvconst_submul(p->coeff, k, p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = bvconst_alloc(k);
      bvconst_clear(aux->coeff, k);
      bvconst_submul(aux->coeff, k, p1->coeff, a);
      aux->prod = r1;

      q->next = aux;
      b->nterms ++;
      q = aux;
    }
    p1 = p1->next;
  }
}


/*
 * Multiply b by b1
 * - b1 must be different from b
 */
void bvarith_buffer_mul_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  bvmlist_t *p, *q;
  uint32_t k;

  assert(b != b1 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);

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
    bvarith_buffer_add_const_times_buffer(b, b1, p->coeff);
    p = p->next;
  }

  // other monomials of p
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    bvarith_buffer_add_mono_times_buffer(b, b1, p->coeff, p->prod);
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
  bvarith_buffer_t aux;

  // hack: we make shallow copy of b into aux
  // then we call mul_buffer.
  aux = *b;
  bvarith_buffer_mul_buffer(b, &aux);
}



/*
 * Add b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
void bvarith_buffer_add_buffer_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, bvarith_buffer_t *b2) {
  bvmlist_t *p1;

  assert(b != b1 && b != b2);
  p1 = b1->list;

  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    bvarith_buffer_add_const_times_buffer(b, b2, p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    bvarith_buffer_add_mono_times_buffer(b, b2, p1->coeff, p1->prod);
    p1 = p1->next;
  }
}


/*
 * Add - b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
void bvarith_buffer_sub_buffer_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, bvarith_buffer_t *b2) {
  bvmlist_t *p1;

  assert(b != b1 && b != b2);
  p1 = b1->list;

  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    bvarith_buffer_sub_const_times_buffer(b, b2, p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    bvarith_buffer_sub_mono_times_buffer(b, b2, p1->coeff, p1->prod);
    p1 = p1->next;
  }  
}



