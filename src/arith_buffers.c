/*
 * BUFFERS FOR OPERATIONS ON POLYNOMIALS
 */

/*
 * Polynomials are represented as sums of pairs <coeff, pp>
 * - the coeff is a rational number.
 * - pp is a power product (cf. power_products.h)
 *
 * In normal form, polynomials have the following properties:
 * - the coefficients are all non zero
 * - the monomials are stored in deg-lex order: lower degree
 *   monomials appear first. Monomials of equal degree are
 *   sorted in lexicographic order.
 *
 * A buffer stores a list of monomials in the deg-lex order.
 * The last element is an end marker, with prod = end_pp (which
 * is larger than any other power product in the deg-lex order).
 */

#include <stdint.h>
#include <assert.h>

#include "arith_buffers.h"




/***********************
 * BUFFER  OPERATIONS  *
 **********************/

/*
 * Initialize store s for list elements
 */
void init_mlist_store(object_store_t *s) {
  init_objstore(s, sizeof(mlist_t), MLIST_BANK_SIZE);
}


/*
 * Delete store s: free all attached memory and clear all rationals.
 * Must not be called unless all buffers with store s are deleted.
 */
static void finalizer(void *l) {
  q_clear(&((mlist_t *) l)->coeff);
}

void delete_mlist_store(object_store_t *s) {
  objstore_delete_finalize(s, finalizer);
}


/*
 * Allocate a list element in s:
 * - initialize the coefficient to 0
 */
static inline mlist_t *alloc_list_elem(object_store_t *s) {
  mlist_t *tmp;

  tmp = (mlist_t *) objstore_alloc(s);
  q_init(&tmp->coeff);
  return tmp;
}

/*
 * Free list element l: free the coefficient first
 */
static inline void free_list_elem(object_store_t *s, mlist_t *l) {
  q_clear(&l->coeff);
  objstore_free(s, l);
}


/*
 * Initialize buffer b to the zero polynomial
 * - ptbl = attached power product table
 * - s = attached store
 * Build the end marker
 */
void init_arith_buffer(arith_buffer_t *b, pprod_table_t *ptbl, object_store_t *s) {
  mlist_t *end;

  b->nterms = 0;
  b->store = s;
  b->ptbl = ptbl;

  end = alloc_list_elem(s);
  end->next = NULL;
  end->prod = end_pp;

  b->list = end;
}


/*
 * Delete b and free all attached memory
 */
void delete_arith_buffer(arith_buffer_t *b) {
  mlist_t *l, *next;

  l = b->list;
  do {
    next = l->next;
    free_list_elem(b->store, l);
    l = next;
  } while (l != NULL);

  b->store = NULL;
  b->ptbl = NULL;
  b->list = NULL;
}



/*
 * Fake start element: return a pointer l such
 * that l->next is b->list.
 */
static inline mlist_t *fake_start(arith_buffer_t *b) {
  mlist_t *l;

  l = ((mlist_t *) &b->list);
  assert(&l->next == &b->list);
  return l;
}


/*
 * Normalize: remove the zero monomials from b
 */
void arith_buffer_normalize(arith_buffer_t *b) {
  mlist_t *p, *q;

  q = fake_start(b);
  p = q->next;
  assert(p == b->list);
  while (p->next != NULL) {
    // p == q->next and p is not the end marker
    assert(p == q->next && p->prod != end_pp);
    if (q_is_zero(&p->coeff)) {
      // remove p
      q->next = p->next;
      free_list_elem(b->store, p);
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
bool arith_buffer_is_constant(arith_buffer_t *b) {
  return b->nterms == 0 || (b->nterms == 1 && b->list->prod == empty_pp);
}


/*
 * Check whether b is constant and nonzero
 * - b must be normalized
 */
bool arith_buffer_is_nonzero(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->prod == empty_pp;
}


/*
 * Check whether b is constant and positive, negative, etc.
 * - b must be normalized
 */
bool arith_buffer_is_pos(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->prod == empty_pp && 
    q_is_pos(&b->list->coeff);
}

bool arith_buffer_is_neg(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->prod == empty_pp && 
    q_is_neg(&b->list->coeff);
}

bool arith_buffer_is_nonneg(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->prod == empty_pp &&
    q_is_nonneg(&b->list->coeff);
}

bool arith_buffer_is_nonpos(arith_buffer_t *b) {
  return b->nterms == 1 && b->list->prod == empty_pp &&
    q_is_nonpos(&b->list->coeff);
}



/*
 * Main monomial = monomial whose pp is the main term
 * - b must be normalized and non zero
 * - this returns the last element in b's monomial list
 */
mlist_t *arith_buffer_main_mono(arith_buffer_t *b) {
  mlist_t *p, *q;

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
uint32_t arith_buffer_degree(arith_buffer_t *b) {
  mlist_t *p;

  if (b->nterms == 0) {
    return 0;
  }

  p = arith_buffer_main_mono(b);
  return pprod_degree(p->prod);
}



/*
 * Main term = maximal power product of b in the deg-lex ordering.
 * - b must be normalized and non zero
 */
pprod_t *arith_buffer_main_term(arith_buffer_t *b) {
  mlist_t *p;

  p = arith_buffer_main_mono(b);
  return p->prod;
}




/*
 * Degree of variable x in b
 * - return largest d such that x^d occurs in b
 * - return 0 if x does not occur in b
 */
uint32_t arith_buffer_var_degree(arith_buffer_t *b, int32_t x) {
  mlist_t *p;
  uint32_t d, e;

  d = 0;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    if (q_is_nonzero(&p->coeff)) {
      e = pprod_var_degree(p->prod, x);
      if (e > d) {
	d = e;
      }
    }
    p = p->next;
  }

  return d;
}


/*
 * Check whether b1 and b2 are equal
 * - both must be normalized and use the same ptbl
 */
bool arith_buffer_equal(arith_buffer_t *b1, arith_buffer_t *b2) {
  mlist_t *p1, *p2;

  assert(b1->ptbl == b2->ptbl);

  if (b1->nterms != b2->nterms) return false;

  p1 = b1->list;
  p2 = b2->list;

  while (p1->prod == p2->prod) {
    if (p1->prod == end_pp) return true;
    if (q_neq(&p1->coeff, &p2->coeff)) return false;
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
 * Reset b to the zero polynomial
 */
void arith_buffer_reset(arith_buffer_t *b) {
  mlist_t *p, *q;

  if (b->nterms == 0) return;

  p = b->list;
  q = p->next;
  while (q != NULL) {
    assert(p->prod != end_pp);
    // p = list element, q = next element
    free_list_elem(b->store, p);
    p = q;
    q = p->next;
  }

  // restore the end marker
  assert(p->prod == end_pp);
  b->list = p;
  b->nterms = 0;
}


/*
 * Multiply b by -1
 */
void arith_buffer_negate(arith_buffer_t *b) {
  mlist_t *p;

  p = b->list;
  while (p->next != NULL) {
    q_neg(&p->coeff);
    p = p->next;
  }
}


/*
 * Multiply b by constant a
 */
void arith_buffer_mul_const(arith_buffer_t *b, rational_t *a) {
  mlist_t *p;

  p = b->list;
  while (p->next != NULL) {
    q_mul(&p->coeff, a);
    p = p->next;
  }
}


/*
 * Divide b by constant a
 * - a must be non-zero
 */
void arith_buffer_div_const(arith_buffer_t *b, rational_t *a) {
  mlist_t *p;

  p = b->list;
  while (p->next != NULL) {
    q_div(&p->coeff, a);
    p = p->next;
  }
}


/*
 * Multiply b by power product r
 */
void arith_buffer_mul_pp(arith_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  mlist_t *p;

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
void arith_buffer_mul_negpp(arith_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  mlist_t *p;

  tbl = b->ptbl;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    p->prod = pprod_mul(tbl, p->prod, r);
    q_neg(&p->coeff);
    p = p->next;
  }
}


/*
 * Multiply b by a * r
 */
void arith_buffer_mul_mono(arith_buffer_t *b, rational_t *a, pprod_t *r) {
  pprod_table_t *tbl;
  mlist_t *p;

  tbl = b->ptbl;
  p = b->list;
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    p->prod = pprod_mul(tbl, p->prod, r);
    q_mul(&p->coeff, a);
    p = p->next;
  }
  
}



/*
 * Add a * r to b
 */
void arith_buffer_add_mono(arith_buffer_t *b, rational_t *a, pprod_t *r) {
  mlist_t *p, *q, *aux;

  if (q_is_zero(a)) return;

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
    q_add(&p->coeff, a);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set(&aux->coeff, a);
    aux->prod = r;

    q->next = aux;
    b->nterms ++;
  }
}


/*
 * Add -a * r to b
 */
void arith_buffer_sub_mono(arith_buffer_t *b, rational_t *a, pprod_t *r) {
  mlist_t *p, *q, *aux;

  if (q_is_zero(a)) return;

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
    q_sub(&p->coeff, a);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set_neg(&aux->coeff, a);
    aux->prod = r;

    q->next = aux;
    b->nterms ++;
  }  
}



/*
 * Add constant a to b
 */
void arith_buffer_add_const(arith_buffer_t *b, rational_t *a) {
  arith_buffer_add_mono(b, a, empty_pp);
}


/*
 * Subtract constant from b
 */
void arith_buffer_sub_const(arith_buffer_t *b, rational_t *a) {
  arith_buffer_sub_mono(b, a, empty_pp);
}


/*
 * Add r to b
 */
void arith_buffer_add_pp(arith_buffer_t *b, pprod_t *r) {
  mlist_t *p, *q, *aux;

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
    q_add_one(&p->coeff);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set_one(&aux->coeff);
    aux->prod = r;

    q->next = aux;
    b->nterms ++;
  }
}


/*
 * Add -r to b
 */
void arith_buffer_sub_pp(arith_buffer_t *b, pprod_t *r) {
  mlist_t *p, *q, *aux;

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
    q_sub_one(&p->coeff);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set_minus_one(&aux->coeff);
    aux->prod = r;

    q->next = aux;
    b->nterms ++;
  }
}


/*
 * Add b1 to b
 */
void arith_buffer_add_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_add(&p->coeff, &p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
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
void arith_buffer_sub_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_sub(&p->coeff, &p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
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
void arith_buffer_add_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_addmul(&p->coeff, &p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      // aux->coeff is initialized to 0 in alloc_list_elem
      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_addmul(&aux->coeff, &p1->coeff, a); 
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
void arith_buffer_sub_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_submul(&p->coeff, &p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      // aux->coeff is initialized to 0 in alloc_list_elem
      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_submul(&aux->coeff, &p1->coeff, a); 
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
void arith_buffer_add_pp_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, pprod_t *r) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_add(&p->coeff, &p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff); 
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
void arith_buffer_sub_pp_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, pprod_t *r) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_sub(&p->coeff, &p1->coeff);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff); 
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
void arith_buffer_add_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, pprod_t *r) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_addmul(&p->coeff, &p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_addmul(&aux->coeff, &p1->coeff, a); // since aux->coeff is 0 initially
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
void arith_buffer_sub_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, pprod_t *r) {
  mlist_t *p, *q, *aux, *p1;
  pprod_t *r1;

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
      q_submul(&p->coeff, &p1->coeff, a);
      q = p;
      p = p->next;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_submul(&aux->coeff, &p1->coeff, a); // since aux->coeff is 0 initially
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
void arith_buffer_mul_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *q;

  assert(b != b1 && b->ptbl == b1->ptbl);

  // keep b's current list of monomials in p
  p = b->list;

  // reset b to the zero polynomial
  q = alloc_list_elem(b->store);
  q->next = NULL;
  q->prod = end_pp;

  b->nterms = 0;
  b->list = q;

  // keep a copy of p in q to cleanup when we're done
  q = p;

  // the constant term of p is first (if any)
  if (p->prod == empty_pp) {
    arith_buffer_add_const_times_buffer(b, b1, &p->coeff);
    p = p->next;
  }

  // other monomials of p
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    arith_buffer_add_mono_times_buffer(b, b1, &p->coeff, p->prod);
    p = p->next;
  }

  // cleanup: free list q
  while (q != NULL) {
    p = q->next;
    free_list_elem(b->store, q);
    q = p;
  }
}


/*
 * Compute the square of b
 */
void arith_buffer_square(arith_buffer_t *b) {
  arith_buffer_t aux;

  // hack: we make shallow copy of b into aux
  // then we call mul_buffer.
  aux = *b;
  arith_buffer_mul_buffer(b, &aux);
}



/*
 * Add b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
void arith_buffer_add_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2) {
  mlist_t *p1;

  assert(b != b1 && b != b2);
  p1 = b1->list;

  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    arith_buffer_add_const_times_buffer(b, b2, &p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    arith_buffer_add_mono_times_buffer(b, b2, &p1->coeff, p1->prod);
    p1 = p1->next;
  }
}


/*
 * Add - b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
void arith_buffer_sub_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2) {
  mlist_t *p1;

  assert(b != b1 && b != b2);
  p1 = b1->list;

  // the constant term of p1 is first
  if (p1->prod == empty_pp) {
    arith_buffer_sub_const_times_buffer(b, b2, &p1->coeff);
    p1 = p1->next;
  }

  while (p1->next != NULL) {
    assert(p1->prod != end_pp);
    arith_buffer_sub_mono_times_buffer(b, b2, &p1->coeff, p1->prod);
    p1 = p1->next;
  }  
}



