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

#include "terms/bv64_constants.h"
#include "terms/bvarith64_buffers.h"
#include "utils/hash_functions.h"




/***********************
 * BUFFER  OPERATIONS  *
 **********************/

/*
 * Initialize store s for list elements
 */
void init_bvmlist64_store(object_store_t *s) {
  init_objstore(s, sizeof(bvmlist64_t), BVMLIST64_BANK_SIZE);
}


/*
 * Delete store s: this must not be called before all
 * buffers that refer to s are deleted.
 */
void delete_bvmlist64_store(object_store_t *s) {
  delete_objstore(s);
}


/*
 * Initialize buffer b to the zero polynomial
 * - ptbl = attached power product table
 * - s = attached store
 * Build the end marker
 */
void init_bvarith64_buffer(bvarith64_buffer_t *b, pprod_table_t *ptbl, object_store_t *s) {
  bvmlist64_t *end;

  b->nterms = 0;
  b->bitsize = 0;
  b->store = s;
  b->ptbl = ptbl;

  end = (bvmlist64_t *) objstore_alloc(s);
  end->next = NULL;
  end->coeff = 0;
  end->prod = end_pp;

  b->list = end;
}


/*
 * Clear b:
 * - free all coefficients.
 * - empty the list (but keep the end marker).
 * - leave bitsize unchanged
 */
static void bvarith64_buffer_clear(bvarith64_buffer_t *b) {
  bvmlist64_t *p, *q;

  if (b->nterms == 0) return;

  p = b->list;
  q = p->next;
  while (q != NULL) {
    assert(p->prod != end_pp);
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
void delete_bvarith64_buffer(bvarith64_buffer_t *b) {
  bvarith64_buffer_clear(b);
  assert(b->list->prod == end_pp);
  objstore_free(b->store, b->list);

  b->store = NULL;
  b->ptbl = NULL;
  b->list = NULL;
}


/*
 * Prepare buffer b: clear b then set bit size equal to n
 */
void bvarith64_buffer_prepare(bvarith64_buffer_t *b, uint32_t n) {
  assert(0 < n && n <=  64);
  if (b->bitsize != 0) {
    bvarith64_buffer_clear(b);
  }

  b->bitsize = n;
}




/*
 * Normalize the coefficients modulo 2^n (set high-order bits to 0)
 * remove the zero monomials from b
 */
void bvarith64_buffer_normalize(bvarith64_buffer_t *b) {
  bvmlist64_t *p;
  bvmlist64_t **q;
  uint32_t n;

  n = b->bitsize;
  q = &b->list;
  p = *q;
  assert(p == b->list);

  while (p->next != NULL) {
    // p == *q and p is not the end marker
    assert(p == *q && p->prod != end_pp);
    p->coeff = norm64(p->coeff, n);
    if (p->coeff == 0) {
      // remove p
      *q = p->next;
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
bool bvarith64_buffer_is_constant(bvarith64_buffer_t *b) {
  return b->nterms == 0 || (b->nterms == 1 && b->list->prod == empty_pp);
}


/*
 * Read the constant term of b as a 64bit integer.
 * - b's bitsize must be between 1 and 64
 * - b must be normalized
 */
uint64_t bvarith64_buffer_get_constant64(bvarith64_buffer_t *b) {
  bvmlist64_t *p;
  uint64_t c;

  c = 0;
  p = b->list;
  if (p->prod == empty_pp) {
    c = p->coeff;
  }

  return c;
}


/*
 * Copy the constant term of b into c
 * - b must be nomralized
 */
void bvarith64_buffer_copy_constant(bvarith64_buffer_t *b, bvconstant_t *c) {
  uint64_t a;

  assert(b->bitsize > 0);

  a = bvarith64_buffer_get_constant64(b);
  bvconstant_copy64(c, b->bitsize, a);
}


/*
 * Main monomial = monomial whose pp is the main term
 * - b must be normalized and non zero
 * - this returns the last element in b's monomial list
 */
bvmlist64_t *bvarith64_buffer_main_mono(bvarith64_buffer_t *b) {
  bvmlist64_t *p, *q;

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
uint32_t bvarith64_buffer_degree(bvarith64_buffer_t *b) {
  bvmlist64_t *p;

  if (b->nterms == 0) {
    return 0;
  }

  p = bvarith64_buffer_main_mono(b);
  return pprod_degree(p->prod);
}



/*
 * Main term = maximal power product of b in the deg-lex ordering.
 * - b must be normalized and non zero
 */
pprod_t *bvarith64_buffer_main_term(bvarith64_buffer_t *b) {
  bvmlist64_t *p;

  p = bvarith64_buffer_main_mono(b);
  return p->prod;
}


/*
 * Check whether b1 and b2 are equal
 * - both must be normalized and use the same ptbl
 */
bool bvarith64_buffer_equal(bvarith64_buffer_t *b1, bvarith64_buffer_t *b2) {
  bvmlist64_t *p1, *p2;

  assert(b1->ptbl == b2->ptbl);

  if (b1->nterms != b2->nterms || b1->bitsize != b2->bitsize) {
    return false;
  }

  p1 = b1->list;
  p2 = b2->list;

  while (p1->prod == p2->prod) {
    if (p1->prod == end_pp) return true;
    if (p1->coeff != p2->coeff) return false;
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
void bvarith64_buffer_set_one(bvarith64_buffer_t *b) {
  bvmlist64_t *p;

  assert(b->bitsize > 0);

  if (b->nterms > 0) {
    bvarith64_buffer_clear(b);
  }

  assert(b->nterms == 0 && b->list->prod == end_pp);

  // new monomial
  p = (bvmlist64_t *) objstore_alloc(b->store);
  p->next = b->list;
  p->prod = empty_pp;
  p->coeff = 1;

  // insert p in the list
  b->list = p;
  b->nterms = 1;
}


/*
 * Assign the constant -1 to b
 */
void bvarith64_buffer_set_minus_one(bvarith64_buffer_t *b) {
  bvmlist64_t *p;

  assert(b->bitsize > 0);

  if (b->nterms > 0) {
    bvarith64_buffer_clear(b);
  }

  assert(b->nterms == 0 && b->list->prod == end_pp);

  // new monomial
  p = (bvmlist64_t *) objstore_alloc(b->store);
  p->next = b->list;
  p->prod = empty_pp;
  p->coeff = ~((uint64_t) 0); // i.e., -1

  // insert p in the list
  b->list = p;
  b->nterms = 1;
}




/*
 * Multiply b by -1
 */
void bvarith64_buffer_negate(bvarith64_buffer_t *b) {
  bvmlist64_t *p;

  assert(b->bitsize > 0);

  p = b->list;
  while (p->next != NULL) {
    p->coeff = - p->coeff;
    p = p->next;
  }
}


/*
 * Multiply b by constant a
 */
void bvarith64_buffer_mul_const(bvarith64_buffer_t *b, uint64_t a) {
  bvmlist64_t *p;

  assert(b->bitsize > 0);

  p = b->list;
  while (p->next != NULL) {
    p->coeff *= a;
    p = p->next;
  }
}


/*
 * Multiply b by power product r
 */
void bvarith64_buffer_mul_pp(bvarith64_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  bvmlist64_t *p;

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
void bvarith64_buffer_mul_negpp(bvarith64_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  bvmlist64_t *p;

  assert(b->bitsize > 0);

  tbl = b->ptbl;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    p->prod = pprod_mul(tbl, p->prod, r);
    p->coeff = - p->coeff;
    p = p->next;
  }
}


/*
 * Multiply b by a * r
 */
void bvarith64_buffer_mul_mono(bvarith64_buffer_t *b, uint64_t a, pprod_t *r) {
  pprod_table_t *tbl;
  bvmlist64_t *p;

  assert(b->bitsize > 0);

  tbl = b->ptbl;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    p->prod = pprod_mul(tbl, p->prod, r);
    p->coeff *= a;
    p = p->next;
  }

}



/*
 * Add a * r to b
 */
void bvarith64_buffer_add_mono(bvarith64_buffer_t *b, uint64_t a, pprod_t *r) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;

  assert(b->bitsize > 0);

  if (a == 0) return;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q points to p0->next, where p0 is p's predecessor (and p0->prod < r)
  // or q points to b->list if p is first in the list.
  if (p->prod == r) {
    p->coeff += a;
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist64_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = a;
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add -a * r to b
 */
void bvarith64_buffer_sub_mono(bvarith64_buffer_t *b, uint64_t a, pprod_t *r) {
  bvarith64_buffer_add_mono(b, -a, r);
}


/*
 * Add constant a to b
 */
void bvarith64_buffer_add_const(bvarith64_buffer_t *b, uint64_t a) {
  bvarith64_buffer_add_mono(b, a, empty_pp);
}


/*
 * Subtract constant from b
 */
void bvarith64_buffer_sub_const(bvarith64_buffer_t *b, uint64_t a) {
  bvarith64_buffer_sub_mono(b, a, empty_pp);
}


/*
 * Add r to b
 */
void bvarith64_buffer_add_pp(bvarith64_buffer_t *b, pprod_t *r) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  if (p->prod == r) {
    p->coeff ++;
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist64_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = 1;
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add -r to b
 */
void bvarith64_buffer_sub_pp(bvarith64_buffer_t *b, pprod_t *r) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  if (p->prod == r) {
    p->coeff --;
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = (bvmlist64_t *) objstore_alloc(b->store);
    aux->next = p;
    aux->coeff = ~((uint64_t) 0); // -1
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add p1 to b
 */
void bvarith64_buffer_add_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  pprod_t *r1;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      p->coeff += p1->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = p1->coeff;
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
void bvarith64_buffer_sub_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  pprod_t *r1;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      p->coeff -= p1->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = - p1->coeff;
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
void bvarith64_buffer_add_const_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, uint64_t a) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  pprod_t *r1;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      p->coeff += a * p1->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = a * p1->coeff;
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
void bvarith64_buffer_sub_const_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, uint64_t a) {
  bvarith64_buffer_add_const_times_mlist(b, p1, -a);
}


/*
 * Add r * p1 to b
 */
void bvarith64_buffer_add_pp_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, pprod_t *r) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  pprod_t *r1;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      p->coeff += p1->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = p1->coeff;
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
void bvarith64_buffer_sub_pp_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, pprod_t *r) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  pprod_t *r1;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      p->coeff -= p1->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = - p1->coeff;
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
void bvarith64_buffer_add_mono_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, uint64_t a, pprod_t *r) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  pprod_t *r1;

  assert(b->bitsize > 0);

  q = &b->list;
  p = *q;

  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      p->coeff += a * p1->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = a * p1->coeff;
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add -a * r * b1 to b
 */
void bvarith64_buffer_sub_mono_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, uint64_t a, pprod_t *r) {
  bvarith64_buffer_add_mono_times_mlist(b, p1, -a, r);
}


/*
 * Multiply b by p1
 * - b1 must be different from b
 */
void bvarith64_buffer_mul_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1) {
  bvmlist64_t *p, *q;

  // keep b's current list of monomials in p
  p = b->list;

  // reset b to the zero polynomial
  q = (bvmlist64_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->prod = end_pp;

  b->nterms = 0;
  b->list = q;

  // keep a copy of p in q to cleanup when we're done
  q = p;

  // the constant term of p is first (if any)
  if (p->prod == empty_pp) {
    bvarith64_buffer_add_const_times_mlist(b, p1, p->coeff);
    p = p->next;
  }

  // other monomials of p
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    bvarith64_buffer_add_mono_times_mlist(b, p1, p->coeff, p->prod);
    p = p->next;
  }

  // cleanup: free list q
  while (q != NULL) {
    p = q->next;
    objstore_free(b->store, q);
    q = p;
  }

}


/*
 * Compute the square of b
 */
void bvarith64_buffer_square(bvarith64_buffer_t *b) {
  bvarith64_buffer_mul_mlist(b, b->list);
}



/*
 * Add p1 * p2 to b
 */
void bvarith64_buffer_add_mlist_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, bvmlist64_t *p2) {
  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    bvarith64_buffer_add_const_times_mlist(b, p2, p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    bvarith64_buffer_add_mono_times_mlist(b, p2, p1->coeff, p1->prod);
    p1 = p1->next;
  }
}


/*
 * Add - p1 * p2 to b
 */
void bvarith64_buffer_sub_mlist_times_mlist(bvarith64_buffer_t *b, bvmlist64_t *p1, bvmlist64_t *p2) {
  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    bvarith64_buffer_sub_const_times_mlist(b, p2, p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    bvarith64_buffer_sub_mono_times_mlist(b, p2, p1->coeff, p1->prod);
    p1 = p1->next;
  }
}


/*
 * Multiply b by p1 ^ d
 * - use aux as an auxiliary buffer.
 * - aux must be distinct from b, but use the same power_product table
 */
void bvarith64_buffer_mul_mlist_power(bvarith64_buffer_t *b, bvmlist64_t *p1, uint32_t d, bvarith64_buffer_t *aux) {
  uint32_t i;

  assert(b != aux && aux->ptbl == b->ptbl);

  if (d <= 4) {
    // small exponent: don't use aux
    for (i=0; i<d; i++) {
      bvarith64_buffer_mul_mlist(b, p1);
      bvarith64_buffer_normalize(b);
    }
  } else {
    // larger exponent
    bvarith64_buffer_prepare(aux, b->bitsize);
    bvarith64_buffer_add_mlist(aux, p1); // aux := p1
    for (;;) {
      /*
       * loop invariant: b0 * p1^d0 == b * aux^d
       * with b0 = b on entry to the function
       *      d0 = d on entry to the function
       */
      assert(d > 0);
      if ((d & 1) != 0) {
        bvarith64_buffer_mul_mlist(b, aux->list); // b := b * aux
        bvarith64_buffer_normalize(b);
      }
      d >>= 1;                               // d := d/2
      if (d == 0) break;
      bvarith64_buffer_square(aux);          // aux := aux^2
      bvarith64_buffer_normalize(aux);
    }
  }
}


/*
 * Extract the content of b as a list of monomials, then reset b to the zero polynomial
 * - b must be normalized
 */
bvmlist64_t *bvarith64_buffer_get_mlist(bvarith64_buffer_t *b) {
  bvmlist64_t *r, *q;

  r = b->list;

  // reset b to the end-marker only
  q = (bvmlist64_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->coeff = 0;
  q->prod = end_pp;

  b->list = q;
  b->nterms = 0;

  return r;
}


/*
 * Hash code for a list of monomials p:
 * - p must be sorted and terminated by the end marker
 * - all coefficients in p must be non-zero and normalized modulo 2^n
 */
uint32_t hash_bvmlist64(bvmlist64_t *p, uint32_t n) {
  uint32_t h, l;

  h = HASH_BVPOLY64_SEED + n;
  while (p->next != NULL) {
    h = jenkins_hash_mix3((uint32_t) (p->coeff >> 32), (uint32_t) p->coeff, h);
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
 */
bool equal_bvmlists64(bvmlist64_t *p1, bvmlist64_t *p2) {
  while (p1->prod == p2->prod) {
    if (p1->prod == end_pp) return true;
    if (p1->coeff != p2->coeff) return false;
    p1 = p1->next;
    p2 = p2->next;
  }

  return false;
}


/*
 * Delete all monomials in *p
 * - store = relevant store (all monomials of p must have been allocated in store).
 */
void free_bvmlist64(bvmlist64_t *p, object_store_t *store) {
  bvmlist64_t *q;

  while (p != NULL) {
    q = p->next;
    objstore_free(store, p);
    p = q;
  }
}





/*************************************
 *  OPERATIONS WITH MONOMIAL ARRAYS  *
 ************************************/

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
static bool good_pprod_array(bvmono64_t *poly, pprod_t **pp) {
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
void bvarith64_buffer_add_bvpoly(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  bvmono64_t *m;
  pprod_t *r1;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m --> monomial (coeff, x_i)
    // the power product for x_i is in *pp
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p --> list element with p->prod >= r1
    // q --> p0->next if p has a predecessor p0 (then p0->prod < r1)
    // q --> b->list if p has no predecessor
    if (p->prod == r1) {
      p->coeff += m->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = m->coeff;
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
 * Subtract poly from buffer b
 */
void bvarith64_buffer_sub_bvpoly(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  bvmono64_t *m;
  pprod_t *r1;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m --> monomial (coeff, x_i)
    // the power product for x_i is in *pp
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p --> list element with p->prod >= r1
    // q --> p0->next if p has a predecessor p0 (then p0->prod < r1)
    // q --> b->list if p has no predecessor
    if (p->prod == r1) {
      p->coeff -= m->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = - m->coeff;
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
void bvarith64_buffer_add_const_times_bvpoly(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp, uint64_t a) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  bvmono64_t *m;
  pprod_t *r1;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m --> monomial (coeff, x_i)
    // the power product for x_i is in *pp
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p --> list element with p->prod >= r1
    // q --> p0->next if p has a predecessor p0 (then p0->prod < r1)
    // q --> b->list if p has no predecessor
    if (p->prod == r1) {
      p->coeff += a * m->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = a * m->coeff;
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
 * Subtract a * poly from buffer b
 */
void bvarith64_buffer_sub_const_times_bvpoly(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp, uint64_t a) {
  bvarith64_buffer_add_const_times_bvpoly(b, poly, pp, -a);
}


/*
 * Add a * r * poly to b
 */
void bvarith64_buffer_add_mono_times_bvpoly(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp, uint64_t a, pprod_t *r) {
  bvmlist64_t *p, *aux;
  bvmlist64_t **q;
  bvmono64_t *m;
  pprod_t *r1;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  m = poly->mono;
  q = &b->list;
  p = *q;

  while (m->var < max_idx) {
    // m --> monomial (coeff, x_i)
    // the power product for x_i is in *pp
    r1 = pprod_mul(b->ptbl, *pp, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p --> list element with p->prod >= r1
    // q --> p0->next if p has a predecessor p0 (then p0->prod < r1)
    // q --> b->list if p has no predecessor
    if (p->prod == r1) {
      p->coeff += a * m->coeff;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = (bvmlist64_t *) objstore_alloc(b->store);
      aux->next = p;
      aux->coeff = a * m->coeff;
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
 * Subtract a * r * poly from b
 */
void bvarith64_buffer_sub_mono_times_bvpoly(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp, uint64_t a, pprod_t *r) {
  bvarith64_buffer_add_mono_times_bvpoly(b, poly, pp, -a, r);
}


/*
 * Multiply b by poly
 */
void bvarith64_buffer_mul_bvpoly(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp) {
  bvmlist64_t *p, *q;

  assert(good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  // keep b's current list of monomials in p
  p = b->list;

  // reset b to the zero polynomial
  q = (bvmlist64_t *) objstore_alloc(b->store);
  q->next = NULL;
  q->prod = end_pp;
  b->nterms = 0;
  b->list = q;

  // keep a copy of p in q to cleanup when we're done
  q = p;

  // deal with p's the constant term if any
  if (p->prod == empty_pp) {
    bvarith64_buffer_add_const_times_bvpoly(b, poly, pp, p->coeff);
    p = p->next;
  }

  // other monomials of p
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    bvarith64_buffer_add_mono_times_bvpoly(b, poly, pp, p->coeff, p->prod);
    p = p->next;
  }

  // cleanup: free list q
  while (q != NULL) {
    p = q->next;
    objstore_free(b->store, q);
    q = p;
  }

}


/*
 * Multiply b by poly ^ d
 * - use aux as an auxiliary buffer (aux must be distinct from b)
 */
void bvarith64_buffer_mul_bvpoly_power(bvarith64_buffer_t *b, bvpoly64_t *poly, pprod_t **pp,
                                       uint32_t d, bvarith64_buffer_t *aux) {
  uint32_t i;

  assert(b != aux && good_pprod_array(poly->mono, pp) && b->bitsize == poly->bitsize);

  if (d <= 4) {
    // small exponent: aux is not used
    for (i=0; i<d; i++) {
      bvarith64_buffer_mul_bvpoly(b, poly, pp);
      bvarith64_buffer_normalize(b);
    }
  } else {
    // larger exponent
    bvarith64_buffer_prepare(aux, b->bitsize);
    bvarith64_buffer_add_bvpoly(aux, poly, pp); // aux := p
    for (;;) {
      /*
       * loop invariant: b0 * p^d0 == b * aux^ d
       * with b0 = b on entry to the function
       *      d0 = d on entry to the function
       */
      assert(d > 0);
      if ((d & 1) != 0) {
        bvarith64_buffer_mul_buffer(b, aux); // b := b * aux
        bvarith64_buffer_normalize(b);
      }
      d >>= 1;                           // d := d/2
      if (d == 0) break;
      bvarith64_buffer_square(aux);        // aux := aux^2
      bvarith64_buffer_normalize(aux);
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
uint32_t hash_bvarith64_buffer(bvarith64_buffer_t *b, int32_t *v) {
  bvmlist64_t *q;
  uint32_t h, n;

  h = HASH_BVPOLY64_SEED + b->nterms;
  n = b->bitsize;
  q = b->list;
  while (q->next != NULL) {
    // coeff in q, variable in v
    h = jenkins_hash_mix3((uint32_t) (q->coeff >> 32), (uint32_t) q->coeff, h);
    h = jenkins_hash_mix3(*v, n, h);

    q = q->next;
    v ++;
  }

  return h;
}



/*
 * Check where P(b, v) is equal to p
 */
bool bvarith64_buffer_equal_bvpoly(bvarith64_buffer_t *b, int32_t *v, bvpoly64_t *p) {
  bvmlist64_t *q;
  bvmono64_t *mono;
  int32_t x1, x2;

  if (b->nterms == p->nterms && b->bitsize == p->bitsize) {
    q = b->list;
    mono = p->mono;
    x1 = *v;
    x2 = mono->var;
    while (x1 == x2) {
      if (x1 == max_idx) return true;
      if (q->coeff != mono->coeff) return false;

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
bvpoly64_t *bvarith64_buffer_get_bvpoly(bvarith64_buffer_t *b, int32_t *v) {
  bvpoly64_t *tmp;
  bvmlist64_t *q, *next;
  uint32_t i, n;

  n = b->nterms;
  tmp = alloc_bvpoly64(n, b->bitsize);

  q = b->list;
  for (i=0; i<n; i++) {
    assert(q->prod != end_pp && v[i] < max_idx);
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
