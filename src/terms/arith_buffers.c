/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

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

#include "utils/hash_functions.h"
#include "terms/arith_buffers.h"



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
 * Normalize: remove the zero monomials from b
 */
void arith_buffer_normalize(arith_buffer_t *b) {
  mlist_t *p;
  mlist_t **q;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (p->next != NULL) {
    // p == *q and p is not the end marker
    assert(p == *q && p->prod != end_pp);
    if (q_is_zero(&p->coeff)) {
      // remove p
      *q = p->next;
      free_list_elem(b->store, p);
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
 * Check whether b is of the form 1 * X for a non-null power-product X
 * If so return X in *r
 */
bool arith_buffer_is_product(arith_buffer_t *b, pprod_t **r) {
  mlist_t *p;

  if (b->nterms == 1) {
    p = b->list;
    if (p->prod != empty_pp && q_is_one(&p->coeff)) {
      assert(p->prod != end_pp);
      *r = p->prod;
      return true;
    }
  }

  return false;
}



/*
 * Check whether b is of the form a * X - a * Y
 * for a non-zero rational a and two products X and Y.
 * If so return X in *r1 and Y in *r2
 */
bool arith_buffer_is_equality(arith_buffer_t *b, pprod_t **r1, pprod_t **r2) {
  mlist_t *p, *q;
  pprod_t *x, *y;
  rational_t a;
  bool is_eq;

  is_eq = false;
  if (b->nterms == 2) {
    p = b->list;
    q = p->next;
    x = p->prod;
    y = p->prod;
    if (x != empty_pp) {
      *r1 = x;
      *r2 = y;
      q_init(&a);
      q_set(&a, &p->coeff);
      q_add(&a, &q->coeff);
      is_eq = q_is_zero(&a);
      q_clear(&a);
    }
  }

  return is_eq;
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
 * Main term = maximal power product of b in the deg-lex ordering.
 * - b must be normalized and non zero
 */
pprod_t *arith_buffer_main_term(arith_buffer_t *b) {
  mlist_t *p;

  p = arith_buffer_main_mono(b);
  return p->prod;
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
 * Monomial of p whose pp equals r (or NULL)
 */
mlist_t *arith_buffer_get_mono(arith_buffer_t *b, pprod_t *r) {
  mlist_t *p;

  p = b->list;
  while (pprod_precedes(p->prod, r)) {
    p = p->next;
  }

  if (p->prod == r) {
    return p;
  } else {
    assert(pprod_precedes(r, p->prod));
    return NULL;
  }
}


/*
 * Constant monomial of p
 */
mlist_t *arith_buffer_get_constant_mono(arith_buffer_t *b) {
  mlist_t *p;

  p = b->list;
  if (p->prod == empty_pp) {
    return p;
  } else {
    return NULL;
  }
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
 * Set b to the constant 1
 */
void arith_buffer_set_one(arith_buffer_t *b) {
  mlist_t *p;

  arith_buffer_reset(b);

  p = alloc_list_elem(b->store);
  p->next = b->list;
  p->prod = empty_pp;
  q_set_one(&p->coeff);

  b->list = p;
  b->nterms = 1;
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
  mlist_t *p, *aux;
  mlist_t **q;

  if (q_is_zero(a)) return;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r, *q == p
  // q is &b->list if p is first in the list
  // q is &p0->next otherwise, where p0 = predecessor of p
  if (p->prod == r) {
    q_add(&p->coeff, a);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set(&aux->coeff, a);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add -a * r to b
 */
void arith_buffer_sub_mono(arith_buffer_t *b, rational_t *a, pprod_t *r) {
  mlist_t *p, *aux;
  mlist_t **q;

  if (q_is_zero(a)) return;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is &b->list if p is first in the list
  // q is &p0->next where p0 = predecessor of p otherwise.
  if (p->prod == r) {
    q_sub(&p->coeff, a);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set_neg(&aux->coeff, a);
    aux->prod = r;

    *q = aux;
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
  mlist_t *p, *aux;
  mlist_t **q;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is either &p->list or &p0->next where p0 is p's predecessor
  if (p->prod == r) {
    q_add_one(&p->coeff);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set_one(&aux->coeff);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add -r to b
 */
void arith_buffer_sub_pp(arith_buffer_t *b, pprod_t *r) {
  mlist_t *p, *aux;
  mlist_t **q;

  q = &b->list;
  p = *q;
  assert(p == b->list);
  while (pprod_precedes(p->prod, r)) {
    q = &p->next;
    p = *q;
  }

  // p points to a monomial with p->prod >= r
  // q is either &p->list or &p0->next where p0 is p's predecessor
  if (p->prod == r) {
    q_sub_one(&p->coeff);
  } else {
    assert(pprod_precedes(r, p->prod));

    aux = alloc_list_elem(b->store);
    aux->next = p;
    q_set_minus_one(&aux->coeff);
    aux->prod = r;

    *q = aux;
    b->nterms ++;
  }
}


/*
 * Add b1 to b
 */
void arith_buffer_add_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  assert(b->ptbl == b1->ptbl);

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_add(&p->coeff, &p1->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add (-b1) to b
 */
void arith_buffer_sub_buffer(arith_buffer_t *b, arith_buffer_t *b1) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_sub(&p->coeff, &p1->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}



/*
 * Add a * b1 to b
 */
void arith_buffer_add_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_addmul(&p->coeff, &p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      // aux->coeff is initialized to 0 in alloc_list_elem
      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_addmul(&aux->coeff, &p1->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add (-a) * b1 to b
 */
void arith_buffer_sub_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = p1->prod;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_submul(&p->coeff, &p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      // aux->coeff is initialized to 0 in alloc_list_elem
      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_submul(&aux->coeff, &p1->coeff, a);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add r * b1 to b
 */
void arith_buffer_add_pp_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, pprod_t *r) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_add(&p->coeff, &p1->coeff);
      //      q = p;
      //      p = p->next;
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set(&aux->coeff, &p1->coeff);
      aux->prod = r1;

      //      q->next = aux;
      //      q = aux;
      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }

}


/*
 * Add - r * b1 to b
 */
void arith_buffer_sub_pp_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, pprod_t *r) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_sub(&p->coeff, &p1->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set_neg(&aux->coeff, &p1->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }
    p1 = p1->next;
  }
}


/*
 * Add a * r * b1 to b
 */
void arith_buffer_add_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, pprod_t *r) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_addmul(&p->coeff, &p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_addmul(&aux->coeff, &p1->coeff, a); // since aux->coeff is 0 initially
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
void arith_buffer_sub_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, pprod_t *r) {
  mlist_t *p, *aux, *p1;
  mlist_t **q;
  pprod_t *r1;

  q = &b->list;
  p = *q;

  p1 = b1->list;
  while (p1->next != NULL) {
    r1 = pprod_mul(b->ptbl, p1->prod, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    if (p->prod == r1) {
      q_submul(&p->coeff, &p1->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_submul(&aux->coeff, &p1->coeff, a); // since aux->coeff is 0 initially
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
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






/****************************************************
 *  OPERATIONS BETWEEN BUFFERS AND MONOMIAL ARRAYS  *
 ***************************************************/

/*
 * All the operations below take three arguments:
 * - b is an arithmetic buffer
 * - p is an array of monomials
 * - q is an array of power products of the same size as p
 *   if p[i] is a monomial a_i x_i then q[i] must be the conversion
 *   of x_i to a power product
 *
 * All operations are in place operations on the first argument b
 * (i.e., all modify the buffer). There are two requirements
 * on p and q:
 * - p must be terminated by and end-marker (var = max_idx).
 * - q must be sorted in the deg-lex ordering.
 */


#ifndef NDEBUG

/*
 * For debugging: check that q contains valid power products
 * sorted in increasing deg-lex ordering.
 */
static bool good_pprod_array(monomial_t *poly, pprod_t **pp) {
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
void arith_buffer_add_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp) {
  mlist_t *p, *aux;
  mlist_t **q;
  pprod_t *r1;

  assert(good_pprod_array(poly, pp));

  q = &b->list;
  p = *q;

  while (poly->var < max_idx) {
    // poly points to a pair (coeff, x_i)
    // r1 = power product for x_i
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q is either &b->list or &p0->next where p0 is the predecessor
    // of p in the list
    if (p->prod == r1) {
      q_add(&p->coeff, &poly->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set(&aux->coeff, &poly->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial of poly
    poly ++;
    pp ++;
  }
}


/*
 * Subtract poly from buffer b
 */
void arith_buffer_sub_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp) {
  mlist_t *p, *aux;
  mlist_t **q;
  pprod_t *r1;

  assert(good_pprod_array(poly, pp));

  q = &b->list;
  p = *q;

  while (poly->var < max_idx) {
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q is either &b->list or &p0->next where p0 is the predecessor
    // of p in the list
    if (p->prod == r1) {
      q_sub(&p->coeff, &poly->coeff);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_set_neg(&aux->coeff, &poly->coeff);
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to next monomial of poly
    poly ++;
    pp ++;
  }
}


/*
 * Add a * poly to buffer b
 */
void arith_buffer_add_const_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a) {
  mlist_t *p, *aux;
  mlist_t **q;
  pprod_t *r1;

  assert(good_pprod_array(poly, pp));

  q = &b->list;
  p = *q;

  while (poly->var < max_idx) {
    // poly points to a pair (coeff, x_i)
    // r1 = power product for x_i
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      q_addmul(&p->coeff, &poly->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_addmul(&aux->coeff, &poly->coeff, a); // aux->coeff is initialized to 0 in alloc_list_elem
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial of poly
    poly ++;
    pp ++;
  }
}


/*
 * Subtract a * poly from b
 */
void arith_buffer_sub_const_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a) {
  mlist_t *p, *aux;
  mlist_t **q;
  pprod_t *r1;

  assert(good_pprod_array(poly, pp));

  q = &b->list;
  p = *q;

  while (poly->var < max_idx) {
    // poly points to a pair (coeff, x_i)
    // r1 = power product for x_i
    r1 = *pp;
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      q_submul(&p->coeff, &poly->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_submul(&aux->coeff, &poly->coeff, a); // aux->coeff is initialized to 0 in alloc_list_elem
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial of poly
    poly ++;
    pp ++;
  }
}


/*
 * Add a * r * poly to buffer b
 */
void arith_buffer_add_mono_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a, pprod_t *r) {
  mlist_t *p, *aux;
  mlist_t **q;
  pprod_t *r1;

  assert(good_pprod_array(poly, pp));

  q = &b->list;
  p = *q;

  while (poly->var < max_idx) {
    // poly points to a pair (coeff, x_i)
    // r1 = r * power product for x_i
    r1 = pprod_mul(b->ptbl, *pp, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      q_addmul(&p->coeff, &poly->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_addmul(&aux->coeff, &poly->coeff, a); // aux->coeff is initialized to 0 in alloc_list_elem
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial of poly
    poly ++;
    pp ++;
  }
}


/*
 * Subtract a * poly from b
 */
void arith_buffer_sub_mono_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a, pprod_t *r) {
  mlist_t *p, *aux;
  mlist_t **q;
  pprod_t *r1;

  assert(good_pprod_array(poly, pp));

  q = &b->list;
  p = *q;

  while (poly->var < max_idx) {
    // poly points to a pair (coeff, x_i)
    // r1 = r * power product for x_i
    r1 = pprod_mul(b->ptbl, *pp, r);
    while (pprod_precedes(p->prod, r1)) {
      q = &p->next;
      p = *q;
    }

    // p points to monomial whose prod is >= r1 in the deg-lex order
    // q points to the predecessor of p in the list
    if (p->prod == r1) {
      q_submul(&p->coeff, &poly->coeff, a);
      q = &p->next;
      p = *q;
    } else {
      assert(pprod_precedes(r1, p->prod));

      aux = alloc_list_elem(b->store);
      aux->next = p;
      q_submul(&aux->coeff, &poly->coeff, a); // aux->coeff is initialized to 0 in alloc_list_elem
      aux->prod = r1;

      *q = aux;
      q = &aux->next;
      b->nterms ++;
    }

    // move to the next monomial of poly
    poly ++;
    pp ++;
  }
}




/*
 * Multiply b by poly
 */
void arith_buffer_mul_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp) {
  mlist_t *p, *q;

  assert(good_pprod_array(poly, pp));

  // keep b's list of monomials in p
  p = b->list;

  // reset b to zero
  q = alloc_list_elem(b->store);
  q->next = NULL;
  q->prod = end_pp;
  b->nterms = 0;
  b->list = q;

  // keep a copy of the list in q to cleanup when we're done
  q = p;

  // constant term if any
  if (p->prod == empty_pp) {
    arith_buffer_add_const_times_monarray(b, poly, pp, &p->coeff);
    p = p->next;
  }

  // rest of p
  while (p->next != NULL) {
    assert(p->prod != end_pp);
    arith_buffer_add_mono_times_monarray(b, poly, pp, &p->coeff, p->prod);
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
 * Multiply b by  p ^ d
 * - pp = power products for the variables of p
 * - use aux as an auxiliary buffer
 * - store the result in b (normalized)
 */
void arith_buffer_mul_monarray_power(arith_buffer_t *b, monomial_t *p, pprod_t **pp, uint32_t d, arith_buffer_t *aux) {
  uint32_t i;

  assert(b != aux);

  if (d <= 4) {
    // small exponent: aux is not used
    for (i=0; i<d; i++) {
      arith_buffer_mul_monarray(b, p, pp);
      arith_buffer_normalize(b);
    }
  } else {
    // larger exponent
    arith_buffer_reset(aux);
    arith_buffer_add_monarray(aux, p, pp); // aux := p
    for (;;) {
      /*
       * loop invariant: b0 * p^d0 == b * aux^ d
       * with b0 = b on entry to the function
       *      d0 = d on entry to the function
       */
      assert(d > 0);
      if ((d & 1) != 0) {
        arith_buffer_mul_buffer(b, aux); // b := b * aux
        arith_buffer_normalize(b);
      }
      d >>= 1;                           // d := d/2
      if (d == 0) break;
      arith_buffer_square(aux);          // aux := aux^2
      arith_buffer_normalize(aux);
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
 * The pair (b, v) defines then a polynomial P(b, v) = a_1 v[1] + ... + a_n v[n],
 */

/*
 * Hash code for P(b, v).
 * This function is consistent with hash_polynomial defined in polynomials.c:
 * If P(b, v) = p0 then hash_arith_buffer(b, v) = hash_polynomial(p0).
 */
uint32_t hash_arith_buffer(arith_buffer_t *b, int32_t *v) {
  mlist_t *q;
  uint32_t h, num, den;

  h = HASH_POLY_SEED + b->nterms;
  q = b->list;
  while (q->next != NULL) {
    // monomial (a_i * x_i) where
    // a_i is q->coeff and x_i is *v
    q_hash_decompose(&q->coeff, &num, &den);
    h = jenkins_hash_triple(*v, num, den, h);

    q = q->next;
    v ++;
  }

  return h;
}



/*
 * Check where P(b, v) is equal to p
 * - both b and p must be normalized.
 */
bool arith_buffer_equal_poly(arith_buffer_t *b, int32_t *v, polynomial_t *p) {
  mlist_t *q;
  monomial_t *mono;
  int32_t x1, x2;

  if (b->nterms == p->nterms) {
    q = b->list;
    mono = p->mono;
    x1 = *v;
    x2 = mono->var;
    while (x1 == x2) {
      if (x1 == max_idx) return true;
      if (q_neq(&q->coeff, &mono->coeff)) return false;

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
polynomial_t *arith_buffer_get_poly(arith_buffer_t *b, int32_t *v) {
  polynomial_t *tmp;
  mlist_t *q, *next;
  uint32_t n, i;

  n = b->nterms;
  tmp = alloc_raw_polynomial(n);

  q = b->list;
  for (i=0; i<n; i++) {
    assert(q->prod != end_pp && v[i] < max_idx);
    // monomial i: coeff = q->coeff, var = v[i]
    tmp->mono[i].var = v[i];
    q_copy_and_clear(&tmp->mono[i].coeff, &q->coeff);

    // delete the list element
    next = q->next;
    objstore_free(b->store, q);
    q = next;
  }

  // empty the monomial list in b
  assert(q->next == NULL && q->prod == end_pp);
  b->nterms = 0;
  b->list = q;

  assert(tmp->mono[n].var == max_idx);

  return tmp;
}

