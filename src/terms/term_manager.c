/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TERM MANAGER
 */

#include <stdint.h>
#include <assert.h>

#include "utils/int_array_sort.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"
#include "utils/bit_tricks.h"
#include "terms/rba_buffer_terms.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"
#include "terms/bit_term_conversion.h"
#include "terms/term_utils.h"

#include "terms/term_manager.h"



/************************
 *  GENERAL OPERATIONS  *
 ***********************/

/*
 * Initialization:
 * - terms = attached term table
 */
void init_term_manager(term_manager_t *manager, term_table_t *terms) {
  manager->terms = terms;
  manager->types = terms->types;
  manager->pprods = terms->pprods;

  manager->arith_buffer = NULL;
  manager->bvarith_buffer = NULL;
  manager->bvarith64_buffer = NULL;
  manager->bvlogic_buffer = NULL;

  manager->bvarith_store = NULL;
  manager->bvarith64_store = NULL;
  manager->nodes = NULL;

  q_init(&manager->r0);
  init_bvconstant(&manager->bv0);
  init_bvconstant(&manager->bv1);
  init_bvconstant(&manager->bv2);
  init_ivector(&manager->vector0, 10);
}


/*
 * Access to the internal stores:
 * - the store is allocated and initialized if needed
 */
node_table_t *term_manager_get_nodes(term_manager_t *manager) {
  node_table_t *tmp;

  tmp = manager->nodes;
  if (tmp == NULL) {
    tmp = (node_table_t *) safe_malloc(sizeof(node_table_t));
    init_node_table(tmp, 0);
    manager->nodes = tmp;
  }

  return tmp;
}

object_store_t *term_manager_get_bvarith_store(term_manager_t *manager) {
  object_store_t *tmp;

  tmp = manager->bvarith_store;
  if (tmp == NULL) {
    tmp = (object_store_t *) safe_malloc(sizeof(object_store_t));
    init_bvmlist_store(tmp);
    manager->bvarith_store = tmp;
  }

  return tmp;
}

object_store_t *term_manager_get_bvarith64_store(term_manager_t *manager) {
  object_store_t *tmp;

  tmp = manager->bvarith64_store;
  if (tmp == NULL) {
    tmp = (object_store_t *) safe_malloc(sizeof(object_store_t));
    init_bvmlist64_store(tmp);
    manager->bvarith64_store = tmp;
  }

  return tmp;
}


/*
 * Access to the internal buffers:
 * - they are allocated and initialized if needed (and the store they need too)
 */
rba_buffer_t *term_manager_get_arith_buffer(term_manager_t *manager) {
  rba_buffer_t *tmp;

  tmp = manager->arith_buffer;
  if (tmp == NULL) {
    tmp = (rba_buffer_t *) safe_malloc(sizeof(rba_buffer_t));
    init_rba_buffer(tmp, manager->pprods);
    manager->arith_buffer = tmp;
  }

  return tmp;
}

bvarith_buffer_t *term_manager_get_bvarith_buffer(term_manager_t *manager) {
  bvarith_buffer_t *tmp;
  object_store_t *mstore;

  tmp = manager->bvarith_buffer;
  if (tmp == NULL) {
    mstore = term_manager_get_bvarith_store(manager);
    tmp = (bvarith_buffer_t *) safe_malloc(sizeof(bvarith_buffer_t));
    init_bvarith_buffer(tmp, manager->pprods, mstore);
    manager->bvarith_buffer = tmp;
  }

  return tmp;
}

bvarith64_buffer_t *term_manager_get_bvarith64_buffer(term_manager_t *manager) {
  bvarith64_buffer_t *tmp;
  object_store_t *mstore;

  tmp = manager->bvarith64_buffer;
  if (tmp == NULL) {
    mstore = term_manager_get_bvarith64_store(manager);
    tmp = (bvarith64_buffer_t *) safe_malloc(sizeof(bvarith64_buffer_t));
    init_bvarith64_buffer(tmp, manager->pprods, mstore);
    manager->bvarith64_buffer = tmp;
  }

  return tmp;
}

bvlogic_buffer_t *term_manager_get_bvlogic_buffer(term_manager_t *manager) {
  bvlogic_buffer_t *tmp;
  node_table_t *nodes;

  tmp = manager->bvlogic_buffer;
  if (tmp == NULL) {
    nodes = term_manager_get_nodes(manager);
    tmp = (bvlogic_buffer_t *) safe_malloc(sizeof(bvlogic_buffer_t));
    init_bvlogic_buffer(tmp, nodes);
    manager->bvlogic_buffer = tmp;
  }

  return tmp;
}


/*
 * Delete all: free memory
 */
static void term_manager_free_nodes(term_manager_t *manager) {
  node_table_t *tmp;

  tmp = manager->nodes;
  if (tmp != NULL) {
    delete_node_table(tmp);
    safe_free(tmp);
    manager->nodes = NULL;
  }
}

static void term_manager_free_bvarith_store(term_manager_t *manager) {
  object_store_t *tmp;

  tmp = manager->bvarith_store;
  if (tmp != NULL) {
    delete_bvmlist_store(tmp);
    safe_free(tmp);
    manager->bvarith_store = NULL;
  }
}

static void term_manager_free_bvarith64_store(term_manager_t *manager) {
  object_store_t *tmp;

  tmp = manager->bvarith64_store;
  if (tmp != NULL) {
    delete_bvmlist64_store(tmp);
    safe_free(tmp);
    manager->bvarith64_store = NULL;
  }
}


static void term_manager_free_arith_buffer(term_manager_t *manager) {
  rba_buffer_t *tmp;

  tmp = manager->arith_buffer;
  if (tmp != NULL) {
    delete_rba_buffer(tmp);
    safe_free(tmp);
    manager->arith_buffer = NULL;
  }
}

static void term_manager_free_bvarith_buffer(term_manager_t *manager) {
  bvarith_buffer_t *tmp;

  tmp = manager->bvarith_buffer;
  if (tmp != NULL) {
    delete_bvarith_buffer(tmp);
    safe_free(tmp);
    manager->bvarith_buffer = NULL;
  }
}

static void term_manager_free_bvarith64_buffer(term_manager_t *manager) {
  bvarith64_buffer_t *tmp;

  tmp = manager->bvarith64_buffer;
  if (tmp != NULL) {
    delete_bvarith64_buffer(tmp);
    safe_free(tmp);
    manager->bvarith64_buffer = NULL;
  }
}

static void term_manager_free_bvlogic_buffer(term_manager_t *manager) {
  bvlogic_buffer_t *tmp;

  tmp = manager->bvlogic_buffer;
  if (tmp != NULL) {
    delete_bvlogic_buffer(tmp);
    safe_free(tmp);
    manager->bvlogic_buffer = NULL;
  }
}


void delete_term_manager(term_manager_t *manager) {
  term_manager_free_arith_buffer(manager);
  term_manager_free_bvarith_buffer(manager);
  term_manager_free_bvarith64_buffer(manager);
  term_manager_free_bvlogic_buffer(manager);

  term_manager_free_bvarith_store(manager);
  term_manager_free_bvarith64_store(manager);
  term_manager_free_nodes(manager);

  q_clear(&manager->r0);
  delete_bvconstant(&manager->bv0);
  delete_bvconstant(&manager->bv1);
  delete_bvconstant(&manager->bv2);
  delete_ivector(&manager->vector0);
}



/*
 * Reset internal buffers and stores
 */
void reset_term_manager(term_manager_t *manager) {
  if (manager->arith_buffer != NULL) {
    reset_rba_buffer(manager->arith_buffer);
  }
  if (manager->bvarith_buffer != NULL) {
    reset_bvarith_buffer(manager->bvarith_buffer);
  }
  if (manager->bvarith64_buffer != NULL) {
    reset_bvarith64_buffer(manager->bvarith64_buffer);
  }
  if (manager->bvlogic_buffer != NULL) {
    bvlogic_buffer_clear(manager->bvlogic_buffer);
  }
  if (manager->bvarith_store != NULL) {
    reset_objstore(manager->bvarith_store);
  }
  if (manager->bvarith64_store != NULL) {
    reset_objstore(manager->bvarith64_store);
  }
  if (manager->nodes != NULL) {
    reset_node_table(manager->nodes);
  }

  q_clear(&manager->r0);
  ivector_reset(&manager->vector0);
}




/************************************************
 *  CONVERSION OF ARRAYS OF BOOLEANS TO TERMS   *
 ***********************************************/

/*
 * Check whether all elements of a are boolean constants
 * - n = size of the array
 */
static bool bvarray_is_constant(const term_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (index_of(a[i]) != bool_const) return false;
    assert(a[i] == true_term || a[i] == false_term);
  }

  return true;
}


/*
 * Convert a to a 64bit value (padded with 0)
 */
static uint64_t bvarray_get_constant64(const term_t *a, uint32_t n) {
  uint64_t c;

  assert(n <= 64);
  c = 0;
  while (n > 0) {
    n --;
    assert(a[n] == true_term || a[n] == false_term);
    c = (c << 1) | (uint64_t) (1 ^ polarity_of(a[n]));
  }

  return c;
}


/*
 * Copy constant array into c
 */
static void bvarray_get_constant(const term_t *a, uint32_t n, bvconstant_t *c) {
  uint32_t i, k;

  assert(n > 64);
  k = (n + 31) >> 5;
  bvconstant_set_bitsize(c, n);

  bvconst_clear(c->data, k);
  for (i=0; i<n; i++) {
    assert(a[i] == true_term || a[i] == false_term);
    if (a[i] == true_term) {
      bvconst_set_bit(c->data, i);
    }
  }
}


/*
 * Check whether term b is (bit i x)
 */
static bool term_is_bit_i(term_table_t *tbl, term_t b, uint32_t i, term_t x) {
  select_term_t *s;

  if (is_pos_term(b) && term_kind(tbl, b) == BIT_TERM) {
    s = bit_term_desc(tbl, b);
    return s->idx == i && s->arg == x;
  }

  return false;
}


/*
 * Check whether b is (bit 0 x) for some x
 * if so return x, otherwise return NULL_TERM
 */
static term_t term_is_bit0(term_table_t *tbl, term_t b) {
  select_term_t *s;

  if (is_pos_term(b) && term_kind(tbl, b) == BIT_TERM) {
    s = bit_term_desc(tbl, b);
    if (s->idx == 0) {
      return s->arg;
    }
  }

  return NULL_TERM;
}


/*
 * Check whether a is of the form (bit 0 x) ... (bit n-1 x)
 * - if so return x
 * - otherwise return NULL_TERM
 */
static term_t bvarray_get_var(term_table_t *tbl, const term_t *a, uint32_t n) {
  term_t x;
  uint32_t i;

  assert(n > 0);

  x = term_is_bit0(tbl, a[0]);
  if (x == NULL_TERM) return x;

  for (i=1; i<n; i++) {
    if (! term_is_bit_i(tbl, a[i], i, x)) {
      return NULL_TERM;
    }
  }

  return x;
}

/*
 * Convert array a to a term
 * - side effect: use bv0
 */
static term_t bvarray_get_term(term_manager_t *manager, const term_t *a, uint32_t n) {
  term_table_t *terms;
  bvconstant_t *bv;
  term_t t;

  assert(n > 0);

  terms = manager->terms;

  if (bvarray_is_constant(a, n)) {
    if (n <= 64) {
      t = bv64_constant(terms, n, bvarray_get_constant64(a, n));
    } else {
      bv = &manager->bv0;
      bvarray_get_constant(a, n, bv);
      assert(bv->bitsize == n);
      t = bvconst_term(terms, n, bv->data);
    }
  } else {
    // try to convert to an existing t
    t = bvarray_get_var(terms, a, n);
    if (t == NULL_TERM || term_bitsize(terms, t) != n) {
      t = bvarray_term(terms, n, a);
    }
  }

  return t;
}



/*
 * BITVECTORS OF SIZE 1
 */

/*
 * Check whether x is equivalent to (bveq a 0b0) or (bveq a 0b1) where a is a term
 * of type (bitvector 1).
 * - if x is (bveq a 0b0): return a and set polarity to false
 * - if x is (bveq a 0b1): return a and set polarity to true
 * - if x is (not (bveq a 0b0)): return a and set polarity to true
 * - if x is (not (bveq a 0b1)): return a and set polarity to false
 * - otherwise, return NULL_TERM (leave polarity unchanged)
 */
static term_t term_is_bveq1(term_table_t *tbl, term_t x, bool *polarity) {
  composite_term_t *eq;
  bvconst64_term_t *c;
  term_t a, b;

  if (term_kind(tbl, x) == BV_EQ_ATOM) {
    eq = bveq_atom_desc(tbl, x);
    a = eq->arg[0];
    b = eq->arg[1];
    if (term_bitsize(tbl, a) == 1) {
      assert(term_bitsize(tbl, b) == 1);
      if (term_kind(tbl, a) == BV64_CONSTANT) {
        // a is either 0b0 or 0b1
        c = bvconst64_term_desc(tbl, a);
        assert(c->value == 0 || c->value == 1);
        *polarity = ((bool) c->value) ^ is_neg_term(x);
        return b;
      }

      if (term_kind(tbl, b) == BV64_CONSTANT) {
        // b is either 0b0 or 0b1
        c = bvconst64_term_desc(tbl, b);
        assert(c->value == 0 || c->value == 1);
        *polarity = ((bool) c->value) ^ is_neg_term(x);
        return a;
      }
    }
  }

  return NULL_TERM;
}


/*
 * Rewrite (bveq [p] [q]) to (eq p q)
 * - t1 and t2 are both bv-arrays of one bit
 * - this is called after checking for simplification (so
 *   we known that (p == q) does not simplify to a single term).
 */
static term_t mk_bveq_arrays1(term_manager_t *manager, term_t t1, term_t t2) {
  composite_term_t *a;
  composite_term_t *b;

  a = bvarray_term_desc(manager->terms, t1);
  b = bvarray_term_desc(manager->terms, t2);

  assert(a->arity == 1 && b->arity == 1);
  return mk_iff(manager, a->arg[0], b->arg[0]);
}


/*
 * Auxiliary function: build (bveq t1 t2)
 * - try to simplify to true or false
 * - attempt to simplify the equality if it's between bit-arrays or bit-arrays and constant
 * - build an atom if no simplification works
 */
static term_t mk_bitvector_eq(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;
  term_t aux;

  tbl = manager->terms;

  if (t1 == t2) return true_term;
  if (disequal_bitvector_terms(tbl, t1, t2)) {
    return false_term;
  }

  /*
   * Try simplifications.  We know that t1 and t2 are not both constant
   * (because disequal_bitvector_terms returned false).
   */
  aux = simplify_bveq(tbl, t1, t2);
  if (aux != NULL_TERM) {
    // Simplification worked
    return aux;
  }

  /*
   * Special case: for bit-vector of size 1
   * - convert to boolean equality
   */
  if (term_bitsize(tbl, t1) == 1 &&
      term_kind(tbl, t1) == BV_ARRAY && term_kind(tbl, t2) == BV_ARRAY) {
    assert(term_bitsize(tbl, t2) == 1);
    return mk_bveq_arrays1(manager, t1, t2);
  }

  /*
   * Default: normalize then build a bveq_atom
   */
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  return bveq_atom(tbl, t1, t2);
}



/*
 * Special constructor for (iff x y) when x or y (or both)
 * are equivalent to (bveq a 0b0) or (bveq a 0b1).
 *
 * Try the following rewrite rules:
 *   iff (bveq a 0b0) (bveq b 0b0) ---> (bveq a b)
 *   iff (bveq a 0b0) (bveq b 0b1) ---> (not (bveq a b))
 *   iff (bveq a 0b1) (bveq b 0b0) ---> (not (bveq a b))
 *   iff (bveq a 0b1) (bveq b 0b1) ---> (bveq a b)
 *
 *   iff (bveq a 0b0) y   ---> (not (bveq a (bvarray y)))
 *   iff (bveq a 0b1) y   ---> (bveq a (bvarray y))
 *
 * return NULL_TERM if none of these rules can be applied
 */
static term_t try_iff_bveq_simplification(term_manager_t *manager, term_t x, term_t y) {
  term_table_t *tbl;
  term_t a, b, t;
  bool pa, pb;

  pa = false;
  pb = false; // to prevent GCC warning

  tbl = manager->terms;

  a = term_is_bveq1(tbl, x, &pa);
  b = term_is_bveq1(tbl, y, &pb);
  if (a != NULL_TERM || b != NULL_TERM) {
    if (a != NULL_TERM && b != NULL_TERM) {
      /*
       * x is (bveq a <constant>)
       * y is (bveq b <constant>)
       */
      t = mk_bitvector_eq(manager, a, b);
      t = signed_term(t, (pa == pb));
      return t;
    }

    if (a != NULL_TERM) {
      /*
       * x is (bveq a <constant>):
       * if pa is true:
       *   (iff (bveq a 0b1) y) --> (bveq a (bvarray y))
       * if pa is false:
       *   (iff (bveq a 0b0) y) --> (not (bveq a (bvarray y)))
       *
       * TODO? We could rewrite to (bveq a (bvarray ~y))??
       */
      t = bvarray_get_term(manager, &y, 1);
      t = mk_bitvector_eq(manager, a, t);
      t = signed_term(t, pa);
      return t;
    }

    if (b != NULL_TERM) {
      /*
       * y is (bveq b <constant>)
       */
      t = bvarray_get_term(manager, &x, 1);
      t = mk_bitvector_eq(manager, b, t);
      t = signed_term(t, pb);
      return t;
    }
  }

  return NULL_TERM;
}




/**********************
 *  ARITHMETIC TERMS  *
 *********************/

/*
 * Arithmetic constant (rational)
 * - r must be normalized
 */
term_t mk_arith_constant(term_manager_t *manager, rational_t *r) {
  return arith_constant(manager->terms, r);
}


/*
 * Convert b to an arithmetic term:
 * - b->ptbl must be equal to manager->pprods
 * - b may be the same as manager->arith_buffer
 * - side effect: b is reset
 *
 * Simplifications (after normalization)
 * - if b is a constant then a constant rational is created
 * - if b is of the form 1. t then t is returned
 * - if b is of the from 1. t_1^d_1 ... t_n^d_n then a power product is returned
 * - otherwise a polynomial term is created
 */
static term_t arith_buffer_to_term(term_table_t *tbl, rba_buffer_t *b) {
  mono_t *m;
  pprod_t *r;
  uint32_t n;
  term_t t;

  assert(b->ptbl == tbl->pprods);

  n = b->nterms;
  if (n == 0) {
    t = zero_term;
  } else if (n == 1) {
    m = rba_buffer_root_mono(b); // unique monomial of b
    r = m->prod;
    if (r == empty_pp) {
      // constant polynomial
      t = arith_constant(tbl, &m->coeff);
    } else if (q_is_one(&m->coeff)) {
      // term or power product
      t =  pp_is_var(r) ? var_of_pp(r) : pprod_term(tbl, r);
    } else {
    // can't simplify
      t = arith_poly(tbl, b);
    }
  } else {
    t = arith_poly(tbl, b);
  }

  reset_rba_buffer(b);

  return t;
}


term_t mk_arith_term(term_manager_t *manager, rba_buffer_t *b) {
  return arith_buffer_to_term(manager->terms, b);
}

term_t mk_direct_arith_term(term_table_t *tbl, rba_buffer_t *b) {
  return arith_buffer_to_term(tbl, b);
}



/*********************************
 *   BOOLEAN-TERM CONSTRUCTORS   *
 ********************************/

/*
 * Simplifications:
 *   x or x       --> x
 *   x or true    --> true
 *   x or false   --> x
 *   x or (not x) --> true
 *
 * Normalization: put smaller index first
 */
term_t mk_binary_or(term_manager_t *manager, term_t x, term_t y) {
  term_t aux[2];

  if (x == y) return x;
  if (x == true_term) return x;
  if (y == true_term) return y;
  if (x == false_term) return y;
  if (y == false_term) return x;
  if (opposite_bool_terms(x, y)) return true_term;

  if (x < y) {
    aux[0] = x; aux[1] = y;
  } else {
    aux[0] = y; aux[1] = x;
  }

  return or_term(manager->terms, 2, aux);
}


/*
 * Rewrite (and x y)  to  (not (or (not x) (not y)))
 */
term_t mk_binary_and(term_manager_t *manager, term_t x, term_t y) {
  return opposite_term(mk_binary_or(manager, opposite_term(x), opposite_term(y)));
}


/*
 * Rewrite (implies x y) to (or (not x) y)
 */
term_t mk_implies(term_manager_t *manager, term_t x, term_t y) {
  return mk_binary_or(manager, opposite_term(x), y);
}


/*
 * Check whether x is uninterpreted or the negation of an uninterpreted boolean term
 */
static inline bool is_literal(term_manager_t *manager, term_t x) {
  return kind_for_idx(manager->terms, index_of(x)) == UNINTERPRETED_TERM;
}


/*
 * Simplifications:
 *    iff x x       --> true
 *    iff x true    --> x
 *    iff x false   --> not x
 *    iff x (not x) --> false
 *
 *    iff (not x) (not y) --> eq x y
 *
 * Optional simplification:
 *    iff (not x) y       --> not (eq x y)  (NOT USED ANYMORE)
 *
 * Smaller index is on the left-hand-side of eq
 */
term_t mk_iff(term_manager_t *manager, term_t x, term_t y) {
  term_t aux;

  if (x == y) return true_term;
  if (x == true_term) return y;
  if (y == true_term) return x;
  if (x == false_term) return opposite_term(y);
  if (y == false_term) return opposite_term(x);
  if (opposite_bool_terms(x, y)) return false_term;

  /*
   * Try iff/bveq simplifications.
   */
  aux = try_iff_bveq_simplification(manager, x, y);
  if (aux != NULL_TERM) {
    return aux;
  }

  /*
   * swap if x > y
   */
  if (x > y) {
    aux = x; x = y; y = aux;
  }

  /*
   * - rewrite (iff (not x) (not y)) to (eq x y)
   * - rewrite (iff (not x) y)       to (eq x (not y))
   *   unless y is uninterpreted and x is not
   */
  if (is_neg_term(x) &&
      (is_neg_term(y) || is_literal(manager, x) || !is_literal(manager, y))) {
    x = opposite_term(x);
    y = opposite_term(y);
  }

  return eq_term(manager->terms, x, y);
}


/*
 * Rewrite (xor x y) to (not (iff x  y))
 *
 * NOTE: used to be (xor x y) to (iff (not x) y)
 */
term_t mk_binary_xor(term_manager_t *manager, term_t x, term_t y) {
  return opposite_term(mk_iff(manager, x, y));
}




/*
 * N-ARY OR/AND
 */

/*
 * Construct (or a[0] ... a[n-1])
 * - all terms are assumed valid and boolean
 * - array a is modified (sorted)
 * - n must be positive
 */
term_t mk_or(term_manager_t *manager, uint32_t n, term_t *a) {
  uint32_t i, j;
  term_t x, y;

  /*
   * Sorting the terms ensure:
   * - true_term shows up first if it's present in a
   *   then false_term if it's present
   *   then all the other boolean terms.
   * - if x and (not x) are both in a, then they occur
   *   at successive positions in a after sorting.
   */
  assert(n > 0);
  int_array_sort(a, n);

  x = a[0];
  if (x == true_term) {
    return true_term;
  }

  j = 0;
  if (x != false_term) {
    //    a[j] = x; NOT NECESSARY
    j ++;
  }

  // remove duplicates and check for x/not x in succession
  for (i=1; i<n; i++) {
    y = a[i];
    if (x != y) {
      if (y == opposite_term(x)) {
        return true_term;
      }
      assert(y != false_term && y != true_term);
      x = y;
      a[j] = x;
      j ++;
    }
  }

  if (j <= 1) {
    // if j = 0, then x = false_term and all elements of a are false
    // if j = 1, then x is the unique non-false term in a
    return x;
  } else {
    return or_term(manager->terms, j, a);
  }
}


/*
 * Construct (and a[0] ... a[n-1])
 * - n must be positive
 * - a is modified
 */
term_t mk_and(term_manager_t *manager, uint32_t n, term_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = opposite_term(a[i]);
  }

  return opposite_term(mk_or(manager, n, a));
}





/*
 * N-ARY XOR
 */

/*
 * Construct (xor a[0] ... a[n-1])
 * - n must be positive
 * - all terms in a must be valid and boolean
 * - a is modified
 */
term_t mk_xor(term_manager_t *manager, uint32_t n, term_t *a) {
  uint32_t i, j;
  term_t x, y;
  bool negate;


  /*
   * First pass: remove true_term/false_term and
   * replace negative terms by their opposite
   */
  negate = false;
  j = 0;
  for (i=0; i<n; i++) {
    x = a[i];
    if (index_of(x) == bool_const) {
      assert(x == true_term || x == false_term);
      negate ^= is_pos_term(x); // flip sign if x is true
    } else {
      assert(x != true_term && x != false_term);
      // apply rule (xor ... (not x) ...) = (not (xor ... x ...))
      negate ^= is_neg_term(x);    // flip sign for (not x)
      x = unsigned_term(x);   // turn (not x) into x
      a[j] = x;
      j ++;
    }
  }

  /*
   * Second pass: remove duplicates (i.e., apply the rule (xor x x) --> false
   */
  n = j;
  int_array_sort(a, n);
  j = 0;
  i = 0;
  while (i+1 < n) {
    x = a[i];
    if (x == a[i+1]) {
      i += 2;
    } else {
      a[j] = x;
      j ++;
      i ++;
    }
  }
  assert(i == n || i + 1 == n);
  if (i+1 == n) {
    a[j] = a[i];
    j ++;
  }


  /*
   * Build the result: (xor negate (xor a[0] ... a[j-1]))
   */
  if (j == 0) {
    return bool2term(negate);
  }

  if (j == 1) {
    return negate ^ a[0];
  }

  if (j == 2) {
    x = a[0];
    y = a[1];
    assert(is_pos_term(x) && is_pos_term(y) && x < y);
    if (negate) {
      /*
       * to be consistent with mk_iff:
       * not (xor x y) --> (eq (not x) y) if y is uninterpreted and x is not
       * not (xor x y) --> (eq x (not y)) otherwise
       */
      if (is_literal(manager, y) && !is_literal(manager, x)) {
        x = opposite_term(x);
      } else {
        y = opposite_term(y);
      }
    }
    return eq_term(manager->terms, x, y);
  }

  // general case: j >= 3
  x = xor_term(manager->terms, j, a);
  if (negate) {
    x = opposite_term(x);
  }

  return x;
}




/******************
 *  IF-THEN-ELSE  *
 *****************/

/*
 * BIT-VECTOR IF-THEN-ELSE
 */

/*
 * Build (ite c x y) when both x and y are boolean constants.
 */
static term_t const_ite_simplify(term_t c, term_t x, term_t y) {
  assert(x == true_term || x == false_term);
  assert(y == true_term || y == false_term);

  if (x == y) return x;
  if (x == true_term) {
    assert(y == false_term);
    return c;
  }

  assert(x == false_term && y == true_term);
  return opposite_term(c);
}


/*
 * Convert (ite c u v) into a bvarray term:
 * - c is a boolean
 * - u and v are two bv64 constants
 */
static term_t mk_bvconst64_ite(term_manager_t *manager, term_t c, bvconst64_term_t *u, bvconst64_term_t *v) {
  uint32_t i, n;
  term_t bu, bv;
  term_t *a;

  n = u->bitsize;
  assert(v->bitsize == n);
  resize_ivector(&manager->vector0, n);
  a = manager->vector0.data;

  for (i=0; i<n; i++) {
    bu = bool2term(tst_bit64(u->value, i)); // bit i of u
    bv = bool2term(tst_bit64(v->value, i)); // bit i of v

    a[i] = const_ite_simplify(c, bu, bv); // a[i] = (ite c bu bv)
  }

  return bvarray_get_term(manager, a, n);
}


/*
 * Same thing with u and v two generic bv constants
 */
static term_t mk_bvconst_ite(term_manager_t *manager, term_t c, bvconst_term_t *u, bvconst_term_t *v) {
  uint32_t i, n;
  term_t bu, bv;
  term_t *a;

  n = u->bitsize;
  assert(v->bitsize == n);
  resize_ivector(&manager->vector0, n);
  a = manager->vector0.data;

  for (i=0; i<n; i++) {
    bu = bool2term(bvconst_tst_bit(u->data, i));
    bv = bool2term(bvconst_tst_bit(v->data, i));

    a[i] = const_ite_simplify(c, bu, bv);
  }

  return bvarray_get_term(manager, a, n);
}



/*
 * Given three boolean terms c, x, and y, check whether (ite c x y)
 * simplifies and if so return the result.
 * - return NULL_TERM if no simplification is found.
 * - the function assumes c is not a boolean constant
 */
static term_t check_ite_simplifies(term_t c, term_t x, term_t y) {
  assert(c != true_term && c != false_term);

  // (ite c x y) --> (ite c true y)  if c == x
  // (ite c x y) --> (ite c false y) if c == not x
  if (c == x) {
    x = true_term;
  } else if (opposite_bool_terms(c, x)) {
    x = false_term;
  }

  // (ite c x y) --> (ite c x false) if c == y
  // (ite c x y) --> (ite c x true)  if c == not y
  if (c == y) {
    y = false_term;
  } else if (opposite_bool_terms(c, y)) {
    y = true_term;
  }

  // (ite c x x) --> x
  // (ite c true false) --> c
  // (ite c false true) --> not c
  if (x == y) return x;
  if (x == true_term && y == false_term) return c;
  if (x == false_term && y == true_term) return opposite_term(c);

  return NULL_TERM;
}


/*
 * Attempt to convert (ite c u v) into a bvarray term:
 * - u is a bitvector constant of no more than 64 bits
 * - v is a bvarray term
 * Return NULL_TERM if the simplifications fail.
 */
static term_t check_ite_bvconst64(term_manager_t *manager, term_t c, bvconst64_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t b;
  term_t *a;

  n = u->bitsize;
  assert(n == v->arity);
  resize_ivector(&manager->vector0, n);
  a = manager->vector0.data;

  for (i=0; i<n; i++) {
    b = bool2term(tst_bit64(u->value, i)); // bit i of u
    b = check_ite_simplifies(c, b, v->arg[i]);

    if (b == NULL_TERM) {
      return NULL_TERM;
    }
    a[i] = b;
  }

  return bvarray_get_term(manager, a, n);
}


/*
 * Same thing for a generic constant u
 */
static term_t check_ite_bvconst(term_manager_t *manager, term_t c, bvconst_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t b;
  term_t *a;

  n = u->bitsize;
  assert(n == v->arity);
  resize_ivector(&manager->vector0, n);
  a = manager->vector0.data;

  for (i=0; i<n; i++) {
    b = bool2term(bvconst_tst_bit(u->data, i)); // bit i of u
    b = check_ite_simplifies(c, b, v->arg[i]);

    if (b == NULL_TERM) {
      return NULL_TERM;
    }
    a[i] = b;
  }

  return bvarray_get_term(manager, a, n);
}


/*
 * Same thing when both u and v are bvarray terms.
 */
static term_t check_ite_bvarray(term_manager_t *manager, term_t c, composite_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t b;
  term_t *a;

  n = u->arity;
  assert(n == v->arity);
  resize_ivector(&manager->vector0, n);
  a = manager->vector0.data;

  for (i=0; i<n; i++) {
    b = check_ite_simplifies(c, u->arg[i], v->arg[i]);

    if (b == NULL_TERM) {
      return NULL_TERM;
    }
    a[i] = b;
  }

  return bvarray_get_term(manager, a, n);
}



/*
 * Build (ite c x y) c is boolean, x and y are bitvector terms
 * Use vector0 as a buffer.
 */
term_t mk_bv_ite(term_manager_t *manager, term_t c, term_t x, term_t y) {
  term_table_t *tbl;
  term_kind_t kind_x, kind_y;
  term_t aux;

  tbl = manager->terms;

  assert(term_type(tbl, x) == term_type(tbl, y) &&
         is_bitvector_term(tbl, x) &&
         is_boolean_term(tbl, c));

  // Try generic simplification first
  if (x == y) return x;
  if (c == true_term) return x;
  if (c == false_term) return y;


  // Check whether (ite c x y) simplifies to a bv_array term
  kind_x = term_kind(tbl, x);
  kind_y = term_kind(tbl, y);
  aux = NULL_TERM;
  switch (kind_x) {
  case BV64_CONSTANT:
    assert(kind_y != BV_CONSTANT);
    if (kind_y == BV64_CONSTANT) {
      return mk_bvconst64_ite(manager, c, bvconst64_term_desc(tbl, x), bvconst64_term_desc(tbl, y));
    }
    if (kind_y == BV_ARRAY) {
      aux = check_ite_bvconst64(manager, c, bvconst64_term_desc(tbl, x), bvarray_term_desc(tbl, y));
    }
    break;

  case BV_CONSTANT:
    assert(kind_y != BV64_CONSTANT);
    if (kind_y == BV_CONSTANT) {
      return mk_bvconst_ite(manager, c, bvconst_term_desc(tbl, x), bvconst_term_desc(tbl, y));
    }
    if (kind_y == BV_ARRAY) {
      aux = check_ite_bvconst(manager, c, bvconst_term_desc(tbl, x), bvarray_term_desc(tbl, y));
    }
    break;

  case BV_ARRAY:
    if (kind_y == BV64_CONSTANT) {
      aux = check_ite_bvconst64(manager, opposite_term(c), bvconst64_term_desc(tbl, y), bvarray_term_desc(tbl, x));
    } else if (kind_y == BV_CONSTANT) {
      aux = check_ite_bvconst(manager, opposite_term(c), bvconst_term_desc(tbl, y), bvarray_term_desc(tbl, x));
    } else if (kind_y == BV_ARRAY) {
      aux = check_ite_bvarray(manager, opposite_term(c), bvarray_term_desc(tbl, y), bvarray_term_desc(tbl, x));
    }
    break;

  default:
    break;
  }

  if (aux != NULL_TERM) {
    return aux;
  }

  /*
   * No simplification found: build a standard ite.
   * Normalize first: (ite (not c) x y) --> (ite c y x)
   */
  if (is_neg_term(c)) {
    c = opposite_term(c);
    aux = x; x = y; y = aux;
  }

  return ite_term(tbl, term_type(tbl, x), c, x, y);
}





/*
 * BOOLEAN IF-THEN-ELSE
 */

/*
 * Build (bv-eq x (ite c y z))
 * - c not true/false
 */
static term_t mk_bveq_ite(term_manager_t *manager, term_t c, term_t x, term_t y, term_t z) {
  term_t ite, aux;

  assert(term_type(manager->terms, x) == term_type(manager->terms, y) &&
         term_type(manager->terms, x) == term_type(manager->terms, z));

  ite = mk_bv_ite(manager, c, y, z);

  // normalize (bveq x ite): put smaller index on the left
  if (x > ite) {
    aux = x; x = ite; ite = aux;
  }

  return bveq_atom(manager->terms, x, ite);
}


/*
 * Special constructor for (ite c (bveq x y) (bveq z u))
 *
 * Apply lift-if rule:
 * (ite c (bveq x y) (bveq x u))  ---> (bveq x (ite c y u))
 */
static term_t mk_lifted_ite_bveq(term_manager_t *manager, term_t c, term_t t, term_t e) {
  term_table_t *tbl;
  composite_term_t *eq1, *eq2;
  term_t x;

  tbl = manager->terms;

  assert(is_pos_term(t) && is_pos_term(e) &&
         term_kind(tbl, t) == BV_EQ_ATOM && term_kind(tbl, e) == BV_EQ_ATOM);

  eq1 = composite_for_idx(tbl, index_of(t));
  eq2 = composite_for_idx(tbl, index_of(e));

  assert(eq1->arity == 2 && eq2->arity == 2);

  x = eq1->arg[0];
  if (x == eq2->arg[0]) return mk_bveq_ite(manager, c, x, eq1->arg[1], eq2->arg[1]);
  if (x == eq2->arg[1]) return mk_bveq_ite(manager, c, x, eq1->arg[1], eq2->arg[0]);

  x = eq1->arg[1];
  if (x == eq2->arg[0]) return mk_bveq_ite(manager, c, x, eq1->arg[0], eq2->arg[1]);
  if (x == eq2->arg[1]) return mk_bveq_ite(manager, c, x, eq1->arg[0], eq2->arg[0]);

  return ite_term(tbl, bool_type(tbl->types), c, t, e);
}


/*
 * Simplifications:
 *  ite c x x        --> x
 *  ite true x y     --> x
 *  ite false x y    --> y
 *
 *  ite c x (not x)  --> (c == x)
 *
 *  ite c c y        --> c or y
 *  ite c x c        --> c and x
 *  ite c (not c) y  --> (not c) and y
 *  ite c x (not c)  --> (not c) or x
 *
 *  ite c true y     --> c or y
 *  ite c x false    --> c and x
 *  ite c false y    --> (not c) and y
 *  ite c x true     --> (not c) or x
 *
 * Otherwise:
 *  ite (not c) x y  --> ite c y x
 */
term_t mk_bool_ite(term_manager_t *manager, term_t c, term_t x, term_t y) {
  term_t aux;

  if (x == y) return x;
  if (c == true_term) return x;
  if (c == false_term) return y;

  if (opposite_bool_terms(x, y)) return mk_iff(manager, c, x);

  if (c == x) return mk_binary_or(manager, c, y);
  if (c == y) return mk_binary_and(manager, c, x);
  if (opposite_bool_terms(c, x)) return mk_binary_and(manager, x, y);
  if (opposite_bool_terms(c, y)) return mk_binary_or(manager, x, y);

  if (x == true_term) return mk_binary_or(manager, c, y);
  if (y == false_term) return mk_binary_and(manager, c, x);
  if (x == false_term) return mk_binary_and(manager, opposite_term(c), y);
  if (y == true_term) return mk_binary_or(manager, opposite_term(c), x);


  if (is_neg_term(c)) {
    c = opposite_term(c);
    aux = x; x = y; y = aux;
  }

  if (is_pos_term(x) && is_pos_term(y) &&
      term_kind(manager->terms, x) == BV_EQ_ATOM &&
      term_kind(manager->terms, y) == BV_EQ_ATOM) {
    return mk_lifted_ite_bveq(manager, c, x, y);
  }

  return ite_term(manager->terms, bool_type(manager->types), c, x, y);
}





/*
 * PUSH IF INSIDE INTEGER POLYNOMIALS
 *
 * If t and e are polynomials with integer variables, we try to
 * rewrite (ite c t e)  to r + a * (ite c t' e')  where:
 *   r = common part of t and e (cf. polynomials.h)
 *   a = gcd of coefficients of (t - r) and (e - r).
 *   t' = (t - r)/a
 *   e' = (e - r)/a
 */

/*
 * Remove every monomial of p whose variable is in a then divide the
 * result by c
 * - a = array of terms sorted in increasing order
 *   a is terminatated by max_idx
 * - every element of a must be a variable of p
 * - c must be non-zero
 * - return the term (p - r)/c
 */
static term_t remove_monomials(term_manager_t *manager, polynomial_t *p, term_t *a, rational_t *c) {
  rba_buffer_t *b;
  monomial_t *mono;
  uint32_t i;
  term_t x;

  assert(q_is_nonzero(c));

  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);

  i = 0;
  mono = p->mono;
  x = mono->var;

  // deal with the constant if any
  if (x == const_idx) {
    if (x == a[i]) {
      i ++;
    } else {
      assert(x < a[i]);
      rba_buffer_add_const(b, &mono->coeff);
    }
    mono ++;
    x = mono->var;
  }

  // non constant monomials
  while (x < max_idx) {
    if (x == a[i]) {
      // skip t
      i ++;
    } else {
      assert(x < a[i]);
      rba_buffer_add_mono(b, &mono->coeff, pprod_for_term(manager->terms, x));
    }
    mono ++;
    x = mono->var;
  }

  // divide by c
  if (! q_is_one(c)) {
    rba_buffer_div_const(b, c);
  }

  // build the term from b
  return arith_buffer_to_term(manager->terms, b);
}


/*
 * Remove every monomial of p whose variable is not in a
 * then add c * t to the result.
 * - a must be an array of terms sorted in increasing order and terminated by max_idx
 * - all elements of a must be variables of p
 */
static term_t add_mono_to_common_part(term_manager_t *manager, polynomial_t *p, term_t *a, rational_t *c, term_t t) {
  term_table_t *tbl;
  rba_buffer_t *b;
  monomial_t *mono;
  uint32_t i;
  term_t x;

  tbl = manager->terms;
  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);

  i = 0;
  mono = p->mono;
  x = mono->var;

  // constant monomial
  if (x == const_idx) {
    assert(x <= a[i]);
    if (x == a[i]) {
      rba_buffer_add_const(b, &mono->coeff);
      i ++;
    }
    mono ++;
    x = mono->var;
  }

  // non constant monomials
  while (x < max_idx) {
    assert(x <= a[i]);
    if (x == a[i]) {
      rba_buffer_add_mono(b, &mono->coeff, pprod_for_term(tbl, x));
      i ++;
    }
    mono ++;
    x = mono->var;
  }

  // add c * t
  rba_buffer_add_mono(b, c, pprod_for_term(tbl, t));

  return arith_buffer_to_term(tbl, b);
}



/*
 * Build  t := p/c where c is a non-zero rational
 */
static term_t polynomial_div_const(term_manager_t *manager, polynomial_t *p, rational_t *c) {
  term_table_t *tbl;
  rba_buffer_t *b;

  tbl = manager->terms;
  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);

  rba_buffer_add_monarray(b, p->mono, pprods_for_poly(tbl, p));
  term_table_reset_pbuffer(tbl);
  rba_buffer_div_const(b, c);

  return arith_buffer_to_term(tbl, b);
}


/*
 * Build t := u * c
 */
static term_t mk_mul_term_const(term_manager_t *manager, term_t t, rational_t *c) {
  term_table_t *tbl;
  rba_buffer_t *b;

  tbl = manager->terms;
  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);
  rba_buffer_add_mono(b, c, pprod_for_term(tbl, t));

  return arith_buffer_to_term(tbl, b);
}


/*
 * Attempt to rewrite (ite c t e) to (r + a * (ite c t' e'))
 * - t and e must be distinct integer polynomials
 * - if r is null and a is one, it builds (ite c t e)
 * - if r is null and a is more than one, it builds a * (ite t' e')
 */
static term_t mk_integer_polynomial_ite(term_manager_t *manager, term_t c, term_t t, term_t e) {
  term_table_t *tbl;
  polynomial_t *p, *q;
  ivector_t *v;
  rational_t *r0;
  term_t ite;

  tbl = manager->terms;

  assert(is_integer_term(tbl, t) && is_integer_term(tbl, e));

  p = poly_term_desc(tbl, t);  // then part
  q = poly_term_desc(tbl, e);  // else part
  assert(! equal_polynomials(p, q));

  /*
   * Collect the common part of p and q into v
   * + the common factor into r0
   */
  v = &manager->vector0;
  ivector_reset(v);
  monarray_pair_common_part(p->mono, q->mono, v);
  ivector_push(v, max_idx); // end marker

  r0 = &manager->r0;
  monarray_pair_non_common_gcd(p->mono, q->mono, r0);
  assert(q_is_pos(r0) && q_is_integer(r0));

  if (v->size > 0) {
    // the common part is non-null
    t = remove_monomials(manager, p, v->data, r0);  // t is (p - common)/r0
    e = remove_monomials(manager, q, v->data, r0);  // e is (q - common)/r0
  } else if (! q_is_one(r0)) {
    // no common part, common factor > 1
    t = polynomial_div_const(manager, p, r0);   // t is p/r0
    e = polynomial_div_const(manager, q, r0);   // e is q/r0
  }

  // build (ite c t e): type int
  ite = ite_term(tbl, int_type(tbl->types), c, t, e);

  if (v->size > 0) {
    // build common + r0 * ite
    ite = add_mono_to_common_part(manager, p, v->data, r0, ite);
  } else if (! q_is_one(r0)) {
    // common factor > 1: build r0 * ite
    ite = mk_mul_term_const(manager, ite, r0);
  }

  // cleanup
  ivector_reset(v);

  return ite;
}



/*
 * PUSH IF INSIDE ARRAY/FUNCTION UPDATES
 *
 * Rewrite rules:
 *  (ite c (update A (i1 ... ik) v) A) --> (update A (i1 ... ik) (ite c v (A i1 ... ik)))
 *  (ite c A (update A (i1 ... ik) v)) --> (update A (i1 ... ik) (ite c (A i1 ... ik) v))
 *  (ite c (update A (i1 ... ik) v) (update A (i1 ... ik) w)) -->
 *      (update A (i1 ... ik) (ite c v w))
 */


/*
 * Auxiliary function: check whether terms a[0...n-1] and b[0 .. n-1] are equal
 */
static bool equal_term_arrays(uint32_t n, const term_t *a, const term_t *b) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}


/*
 * Check whether one of the rewrite rules above is applicable to (ite c t e tau)
 * - t and e have a function type
 * - it it is apply it and return the result
 * - otherwise, return NULL_TERM
 */
static term_t simplify_ite_update(term_manager_t *manager, term_t c, term_t t, term_t e, type_t tau) {
  term_table_t *terms;
  composite_term_t *update1, *update2;
  bool t_is_update, e_is_update;
  uint32_t n;
  term_t aux;
  type_t sigma;

  terms = manager->terms;

  assert(is_function_term(terms, t) && is_function_term(terms, e));

  t_is_update = (term_kind(terms, t) == UPDATE_TERM);
  e_is_update = (term_kind(terms, e) == UPDATE_TERM);
  sigma = function_type_range(manager->types, tau);

  if (t_is_update && e_is_update) {
    update1 = update_term_desc(terms, t);
    update2 = update_term_desc(terms, e);

    n = update1->arity;
    assert(n >= 3 && n == update2->arity);

    if (equal_term_arrays(n-1, update1->arg, update2->arg)) {
      // t is (update f a[1] ... a[n-2] v)
      // e is (update f a[1] ... a[n-2] w)
      aux = mk_ite(manager, c, update1->arg[n-1], update2->arg[n-1], sigma); // (ite c v w)
      return mk_update(manager, update1->arg[0], n-2, update1->arg + 1, aux);
    }

  } else if (t_is_update) {
    update1 = update_term_desc(terms, t);
    if (update1->arg[0] == e) {
      // t is (update e a[1] ... a[n-2] v)
      // (ite c t e) --> (update e a[1] ... a[n-2] (ite c v (e a[1] ... a[n-2])))
      n = update1->arity;
      assert(n >= 3);

      aux = mk_application(manager, e, n-2, update1->arg + 1);   // (e a[1] ... a[n-2])
      aux = mk_ite(manager, c, update1->arg[n-1], aux, sigma);   // (ite c v (e a[1] ... a[n-2]))
      return mk_update(manager, e, n-2, update1->arg + 1, aux);
    }

  } else if (e_is_update) {
    update2 = update_term_desc(terms, e);
    if (update2->arg[0] == t) {
      // e is (update t a[1] ... a[n-2] w)
      // (ite c t e) --> (update t a[1] ... a[n-2] (ite c (t (a[1] ... a[n-2]) w)))
      n = update2->arity;
      assert(n >= 3);

      aux = mk_application(manager, t, n-2, update2->arg + 1);   // (t a[1] ... a[n-2])
      aux = mk_ite(manager, c, aux, update2->arg[n-1], sigma);   // (ite c (t a[1] ... a[n-2]) w)
      return mk_update(manager, t, n-2, update2->arg + 1, aux);
    }
  }

  return NULL_TERM;
}




/*
 * GENERIC IF-THEN-ELSE
 */

/*
 * Simplify t assuming c holds
 * - c must be a boolean term.
 *
 * Rules:
 *   (ite  c x y) --> x
 *   (ite ~c x y) --> y
 */
static term_t simplify_in_context(term_table_t *tbl, term_t c, term_t t) {
  composite_term_t *d;

  assert(is_boolean_term(tbl, c) && good_term(tbl, t));

  while (is_ite_term(tbl, t)) {
    d = ite_term_desc(tbl, t);
    if (d->arg[0] == c) {
      t = d->arg[1];
    } else if (opposite_bool_terms(c, d->arg[0])) {
      t = d->arg[2];
    } else {
      break;
    }
  }

  return t;
}


/*
 * If-then-else: (if c then t else e)
 * - c must be Boolean
 * - t and e must have compatible types tau1 and tau2
 * - tau must be the least common supertype of tau1 and tau2
 *
 * Simplifications
 *    ite c (ite  c x y) z  --> ite c x z
 *    ite c (ite ~c x y) z  --> ite c y z
 *    ite c x (ite  c y z)  --> ite c x z
 *    ite c x (ite ~c y z)  --> ite c x y
 *
 *    ite true x y   --> x
 *    ite false x y  --> y
 *    ite c x x      --> x
 *
 * Otherwise:
 *    ite (not c) x y --> ite c y x
 *
 * Plus special trick for integer polynomials:
 *    ite c (d * p1) (d * p2) --> d * (ite c p1 p2)
 *
 */
term_t mk_ite(term_manager_t *manager, term_t c, term_t t, term_t e, type_t tau) {
  term_t aux;

  // boolean ite
  if (is_boolean_type(tau)) {
    assert(is_boolean_term(manager->terms, t) &&
           is_boolean_term(manager->terms, e));
    return mk_bool_ite(manager, c, t, e);
  }

  // bit-vector ite
  if (is_bv_type(manager->types, tau)) {
    assert(is_bitvector_term(manager->terms, t) &&
           is_bitvector_term(manager->terms, e));
    return mk_bv_ite(manager, c, t, e);
  }

  // general case
  if (c == true_term) return t;
  if (c == false_term) return e;

  t = simplify_in_context(manager->terms, c, t);
  e = simplify_in_context(manager->terms, opposite_term(c), e);
  if (t == e) return t;

  if (is_neg_term(c)) {
    // ite (not c) x y  --> ite c y x
    c = opposite_term(c);
    aux = t; t = e; e = aux;
  }

  // check whether both sides are integer polynomials
  if (is_integer_type(tau)
      && term_kind(manager->terms, t) == ARITH_POLY
      && term_kind(manager->terms, e) == ARITH_POLY) {
    return mk_integer_polynomial_ite(manager, c, t, e);
  }

  // check for array updates
  if (is_function_type(manager->types, tau)) {
    aux = simplify_ite_update(manager, c, t, e, tau);
    if (aux != NULL_TERM) return aux;
  }

  return ite_term(manager->terms, tau, c, t, e);
}





/**********************
 *  ARITHMETIC ATOMS  *
 *********************/

/*
 * Auxiliary function: try to simplify (t1 == t2)
 * using the following rules:
 *   (ite c x y) == x -->  c  provided x != y holds
 *   (ite c x y) == y --> ~c  provided x != y holds
 *
 * - return the result if one of these rules apply
 * - return NULL_TERM otherwise.
 */
static term_t check_aritheq_simplifies(term_table_t *tbl, term_t t1, term_t t2) {
  composite_term_t *d;
  term_t x, y;

  assert(is_arithmetic_term(tbl, t1) && is_arithmetic_term(tbl, t2));

  if (is_ite_term(tbl, t1)) {
    // (ite c x y) == t2
    d = ite_term_desc(tbl, t1);
    x = d->arg[1];
    y = d->arg[2];
    if (x == t2 && disequal_arith_terms(tbl, y, t2)) {
      return d->arg[0];
    }
    if (y == t2 && disequal_arith_terms(tbl, x, t2)) {
      return opposite_term(d->arg[0]);
    }
  }

  if (is_ite_term(tbl, t2)) {
    // t1 == (ite c x y)
    d = ite_term_desc(tbl, t2);
    x = d->arg[1];
    y = d->arg[2];
    if (x == t1 && disequal_arith_terms(tbl, y, t1)) {
      return d->arg[0];
    }
    if (y == t1 && disequal_arith_terms(tbl, x, t1)) {
      return opposite_term(d->arg[0]);
    }
  }

  return NULL_TERM;
}


/*
 * Auxiliary function: build binary equality (t1 == t2)
 * for two arithmetic terms t1 and t2.
 * - try simplification and normalize first
 */
static term_t mk_arith_bineq_atom(term_table_t *tbl, term_t t1, term_t t2) {
  term_t aux;

  assert(is_arithmetic_term(tbl, t1) && is_arithmetic_term(tbl, t2));

  if (disequal_arith_terms(tbl, t1, t2)) {
    return false_term;
  }

  aux = check_aritheq_simplifies(tbl, t1, t2);
  if (aux != NULL_TERM) {
    return aux;
  }

  // normalize: put the smallest term on the left
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  return arith_bineq_atom(tbl, t1, t2);
}



/*
 * Construct the atom (b == 0) then reset b.
 *
 * Normalize b first.
 * - simplify to true if b is the zero polynomial
 * - simplify to false if b is constant and non-zero
 * - rewrite to (t1 == t2) if that's possible.
 * - otherwise, create a polynomial term t from b
 *   and return the atom (t == 0).
 */
term_t mk_arith_eq0(term_manager_t *manager, rba_buffer_t *b) {
  term_table_t *tbl;
  mono_t *m[2], *m1, *m2;
  pprod_t *r1, *r2;
  rational_t *r0;
  term_t t1, t2, t;
  uint32_t n;

  assert(b->ptbl == manager->pprods);

  tbl = manager->terms;

  n = b->nterms;
  if (n == 0) {
    // b is zero
    t = true_term;

  } else if (n == 1) {
    /*
     * b is a1 * r1 with a_1 != 0
     * (a1 * r1 == 0) is false if r1 is the empty product
     * (a1 * r1 == 0) simplifies to (r1 == 0) otherwise
     */
    m1 = rba_buffer_root_mono(b);
    r1 = m1->prod;
    assert(q_is_nonzero(&m1->coeff));
    if (r1 == empty_pp) {
      t = false_term;
    } else {
      t1 = pp_is_var(r1) ? var_of_pp(r1) : pprod_term(tbl, r1);
      t = mk_arith_bineq_atom(tbl, zero_term, t1); // atom r1 = 0
    }

  } else if (n == 2) {
    /*
     * b is a1 * r1 + a2 * r2
     * Simplifications:
     * - rewrite (b == 0) to (r2 == -a1/a2) if r1 is the empty product
     * - rewrite (b == 0) to (r1 == r2) is a1 + a2 = 0
     */
    rba_buffer_monomial_pair(b, m);
    m1 = m[0];
    m2 = m[1];
    r1 = m1->prod;
    r2 = m2->prod;
    assert(q_is_nonzero(&m1->coeff) && q_is_nonzero(&m2->coeff));

    r0 = &manager->r0;

    if (r1 == empty_pp) {
      q_set_neg(r0, &m1->coeff);
      q_div(r0, &m2->coeff);  // r0 is -a1/a2
      t1 = arith_constant(tbl, r0);
      t2 = pp_is_var(r2) ? var_of_pp(r2) : pprod_term(tbl, r2);
      t = mk_arith_bineq_atom(tbl, t1, t2);

    } else {
      q_set(r0, &m1->coeff);
      q_add(r0, &m2->coeff);
      if (q_is_zero(r0)) {
        t1 = pp_is_var(r1) ? var_of_pp(r1) : pprod_term(tbl, r1);
        t2 = pp_is_var(r2) ? var_of_pp(r2) : pprod_term(tbl, r2);
        t = mk_arith_bineq_atom(tbl, t1, t2);

      } else {
        // no simplification
        t = arith_poly(tbl, b);
        t = arith_eq_atom(tbl, t);
      }
    }

  } else {
    /*
     * more than 2 monomials: don't simplify
     */
    t = arith_poly(tbl, b);
    t = arith_eq_atom(tbl, t);
  }


  reset_rba_buffer(b);
  assert(good_term(tbl, t) && is_boolean_term(tbl, t));

  return t;
}




/*
 * Auxiliary function: try to simplify (t >= 0)
 * using the following rules:
 *   (ite c x y) >= 0 --> c     if x >= 0 and y < 0
 *   (ite c x y) >= 0 --> ~c    if x < 0 and y >= 0
 *
 * return NULL_TERM if these simplifications don't work.
 * return the result otherwise
 */
static term_t check_arithge_simplifies(term_table_t *tbl, term_t t) {
  composite_term_t *d;
  term_t x, y;

  assert(is_arithmetic_term(tbl, t));

  if (is_ite_term(tbl, t)) {
    d = ite_term_desc(tbl, t);
    x = d->arg[1];
    y = d->arg[2];

    if (arith_term_is_nonneg(tbl, x) &&
        arith_term_is_negative(tbl, y)) {
      return d->arg[0];
    }

    if (arith_term_is_negative(tbl, x) &&
        arith_term_is_nonneg(tbl, y)) {
      return opposite_term(d->arg[0]);
    }
  }

  return NULL_TERM;
}


/*
 * Build the atom (t >= 0)
 * - try simplifications first
 */
static term_t mk_arith_geq_atom(term_table_t *tbl, term_t t) {
  term_t aux;

  assert(is_arithmetic_term(tbl, t));

  if (arith_term_is_nonneg(tbl, t)) {
    return true_term;
  }

  aux = check_arithge_simplifies(tbl, t);
  if (aux != NULL_TERM) {
    return aux;
  }

  return arith_geq_atom(tbl, t);
}



/*
 * Construct the atom (b >= 0) then reset b.
 *
 * Normalize b first then check for simplifications.
 * - simplify to true or false if b is a constant
 * - otherwise build a term t from b and return the atom (t >= 0)
 */
term_t mk_direct_arith_geq0(term_table_t *tbl, rba_buffer_t *b) {
  mono_t *m;
  pprod_t *r;
  term_t t;
  uint32_t n;

  assert(b->ptbl == tbl->pprods);

  n = b->nterms;
  if (n == 0) {
    // b is zero
    t = true_term;
  } else if (n == 1) {
    /*
     * b is a * r with a != 0
     * if r is the empty product, (b >= 0) simplifies to true or false
     * otherwise, (b >= 0) simplifies either to r >= 0 or -r >= 0
     */
    m = rba_buffer_root_mono(b); // unique monomial of b
    r = m->prod;
    if (q_is_pos(&m->coeff)) {
      // a > 0
      if (r == empty_pp) {
        t = true_term;
      } else {
        t = pp_is_var(r) ? var_of_pp(r) : pprod_term(tbl, r);
        t = mk_arith_geq_atom(tbl, t); // r >= 0
      }
    } else {
      // a < 0
      if (r == empty_pp) {
        t = false_term;
      } else {
        q_set_minus_one(&m->coeff); // force a := -1
        t = arith_poly(tbl, b);
        t = mk_arith_geq_atom(tbl, t);
      }
    }

  } else {
    // no simplification (for now).
    // could try to reduce the coefficients?
    t = arith_poly(tbl, b);
    t = mk_arith_geq_atom(tbl, t);
  }

  reset_rba_buffer(b);
  assert(good_term(tbl, t) && is_boolean_term(tbl, t));

  return t;
}


/*
 * Same thing: using a manager
 */
term_t mk_arith_geq0(term_manager_t *manager, rba_buffer_t *b) {
  return mk_direct_arith_geq0(manager->terms, b);
}


/*
 * Cheap lift-if decomposition:
 * - decompose (ite c x y) (ite c z u) ---> [c, x, z, y, u]
 * - decompose (ite c x y) z           ---> [c, x, z, y, z]
 * - decompose x (ite c y z)           ---> [c, x, y, x, z]
 *
 * The result is stored into the lift_result_t object:
 * - for example: [c, x, z, y, u] is stored as
 *    cond = c,  left1 = x, left2 = z,  right1 = y, right2 = u
 * - the function return true if the decomposition succeeds, false otherwise
 *
 * NOTE: we don't want to apply these lift-if rules if one or both terms
 * are special if-then-elses.
 */
typedef struct lift_result_s {
  term_t cond;
  term_t left1, left2;
  term_t right1, right2;
} lift_result_t;


static bool check_for_lift_if(term_table_t *tbl, term_t t1, term_t t2, lift_result_t *d) {
  composite_term_t *ite1, *ite2;
  term_t cond;

  assert(is_pos_term(t1) && is_pos_term(t2));

  if (term_kind(tbl, t1) == ITE_TERM) {
    if (term_kind(tbl, t2) == ITE_TERM) {
      // both are (if-then-else ..)
      ite1 = ite_term_desc(tbl, t1);
      ite2 = ite_term_desc(tbl, t2);

      cond = ite1->arg[0];
      if (cond == ite2->arg[0]) {
        d->cond = cond;
        d->left1 = ite1->arg[1];
        d->left2 = ite2->arg[1];
        d->right1 = ite1->arg[2];
        d->right2 = ite2->arg[2];
        return true;
      }

    } else {
      // t1 is (if-then-else ..) t2 is not
      ite1 = ite_term_desc(tbl, t1);
      d->cond = ite1->arg[0];
      d->left1 = ite1->arg[1];
      d->left2 = t2;
      d->right1 = ite1->arg[2];
      d->right2 = t2;
      return true;

    }
  } else if (term_kind(tbl, t2) == ITE_TERM) {
    // t2 is (if-then-else ..) t1 is not

    ite2 = ite_term_desc(tbl, t2);
    d->cond = ite2->arg[0];
    d->left1 = t1;
    d->left2 = ite2->arg[1];
    d->right1 = t1;
    d->right2 = ite2->arg[2];
    return true;
  }

 return false;
}






/*
 * Store t1 - t2 in buffer b
 */
static void mk_arith_diff(term_manager_t *manager, rba_buffer_t *b, term_t t1, term_t t2) {
  reset_rba_buffer(b);
  rba_buffer_add_term(b, manager->terms, t1);
  rba_buffer_sub_term(b, manager->terms, t2);
}


/*
 * Build the term (ite c (aritheq t1 t2) (aritheq t3 t4))
 * - c is a boolean term
 * - t1, t2, t3, t4 are all arithmetic terms
 */
static term_t mk_lifted_aritheq(term_manager_t *manager, term_t c, term_t t1, term_t t2, term_t t3, term_t t4) {
  rba_buffer_t *b;
  term_t left, right;

  b = term_manager_get_arith_buffer(manager);

  mk_arith_diff(manager, b, t1, t2);
  left = mk_arith_eq0(manager, b);
  mk_arith_diff(manager, b, t3, t4);
  right = mk_arith_eq0(manager, b);

  return mk_bool_ite(manager, c, left, right);
}

// Variant: apply the cheap lift-if rules recursively
static term_t mk_lifted_aritheq_recur(term_manager_t *manager, term_t c, term_t t1, term_t t2, term_t t3, term_t t4) {
  term_t left, right;

  left = mk_arith_eq(manager, t1, t2);
  right = mk_arith_eq(manager, t3, t4);
  return mk_bool_ite(manager, c, left, right);
}


/*
 * Build the term (ite c (arithge t1 t2) (arithge t3 t4))
 * - c is a boolean term
 * - t1, t2, t3, t4 are all arithmetic terms
 */
static term_t mk_lifted_arithgeq(term_manager_t *manager, term_t c, term_t t1, term_t t2, term_t t3, term_t t4) {
  rba_buffer_t *b;
  term_t left, right;

  b = term_manager_get_arith_buffer(manager);

  mk_arith_diff(manager, b, t1, t2);
  left = mk_arith_geq0(manager, b);
  mk_arith_diff(manager, b, t3, t4);
  right = mk_arith_geq0(manager, b);

  return mk_bool_ite(manager, c, left, right);
}

// Variant: apply the cheap lift-if rules recursively
static term_t mk_lifted_arithgeq_recur(term_manager_t *manager, term_t c, term_t t1, term_t t2, term_t t3, term_t t4) {
  term_t left, right;

  left = mk_arith_geq(manager, t1, t2);
  right = mk_arith_geq(manager, t3, t4);
  return mk_bool_ite(manager, c, left, right);
}



/*
 * BINARY ATOMS
 */

/*
 * Equality term (= t1 t2)
 *
 * Apply the cheap lift-if rules
 *  (eq x (ite c y z))  ---> (ite c (eq x y) (eq x z)) provided x is not an if term
 *  (eq (ite c x y) z)) ---> (ite c (eq x z) (eq y z)) provided z is not an if term
 *  (eq (ite c x y) (ite c z u)) --> (ite c (eq x z) (eq y u))
 *
 */
term_t mk_arith_eq(term_manager_t *manager, term_t t1, term_t t2) {
  rba_buffer_t *b;
  lift_result_t tmp;

  assert(is_arithmetic_term(manager->terms, t1) &&
         is_arithmetic_term(manager->terms, t2));

  if (false && check_for_lift_if(manager->terms, t1, t2, &tmp)) {
    if (true) {
      return mk_lifted_aritheq(manager, tmp.cond, tmp.left1, tmp.left2, tmp.right1, tmp.right2);
    } else {
      return mk_lifted_aritheq_recur(manager, tmp.cond, tmp.left1, tmp.left2, tmp.right1, tmp.right2);
    }
  }

  b = term_manager_get_arith_buffer(manager);
  mk_arith_diff(manager, b, t1, t2);
  return mk_arith_eq0(manager, b);
}


/*
 * Inequality: (>= t1 t2)
 *
 * Try the cheap lift-if rules.
 */
term_t mk_arith_geq(term_manager_t *manager, term_t t1, term_t t2) {
  rba_buffer_t *b;
  lift_result_t tmp;

  assert(is_arithmetic_term(manager->terms, t1) &&
         is_arithmetic_term(manager->terms, t2));

  if (false && check_for_lift_if(manager->terms, t1, t2, &tmp)) {
    if (true) {
      return mk_lifted_arithgeq(manager, tmp.cond, tmp.left1, tmp.left2, tmp.right1, tmp.right2);
    } else {
      return mk_lifted_arithgeq_recur(manager, tmp.cond, tmp.left1, tmp.left2, tmp.right1, tmp.right2);
    }
  }

  b = term_manager_get_arith_buffer(manager);
  mk_arith_diff(manager, b, t1, t2);
  return mk_arith_geq0(manager, b);
}


/*
 * Derived atoms
 */

// t1 != t2  -->  not (t1 == t2
term_t mk_arith_neq(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_arith_eq(manager, t1, t2));
}

// t1 <= t2  -->  t2 >= t1
term_t mk_arith_leq(term_manager_t *manager, term_t t1, term_t t2) {
  return mk_arith_geq(manager, t2, t1);
}

// t1 > t2  -->  not (t2 >= t1)
term_t mk_arith_gt(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_arith_geq(manager, t2, t1));
}

// t1 < t2  -->  not (t1 >= t2)
term_t mk_arith_lt(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_arith_geq(manager, t1, t2));
}


// b != 0   -->  not (b == 0)
term_t mk_arith_neq0(term_manager_t *manager, rba_buffer_t *b) {
  return opposite_term(mk_arith_eq0(manager, b));
}

// b <= 0  -->  (- b) >= 0
term_t mk_arith_leq0(term_manager_t *manager, rba_buffer_t *b) {
  rba_buffer_negate(b);
  return mk_arith_geq0(manager, b);
}

// b > 0  -->  not (b <= 0)
term_t mk_arith_gt0(term_manager_t *manager, rba_buffer_t *b) {
  return opposite_term(mk_arith_leq0(manager, b));
}

// b < 0  -->  not (b >= 0)
term_t mk_arith_lt0(term_manager_t *manager, rba_buffer_t *b) {
  return opposite_term(mk_arith_geq0(manager, b));
}


/*
 * Variants: use a term t
 */
// t == 0
term_t mk_arith_term_eq0(term_manager_t *manager, term_t t) {
  rba_buffer_t *b;

  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);
  rba_buffer_add_term(b, manager->terms, t);

  return mk_arith_eq0(manager, b);
}

// t != 0
term_t mk_arith_term_neq0(term_manager_t *manager, term_t t) {
  rba_buffer_t *b;

  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);
  rba_buffer_add_term(b, manager->terms, t);

  return mk_arith_neq0(manager, b);
}

// t >= 0
term_t mk_arith_term_geq0(term_manager_t *manager, term_t t) {
  rba_buffer_t *b;

  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);
  rba_buffer_add_term(b, manager->terms, t);

  return mk_arith_geq0(manager, b);
}

// t <= 0
term_t mk_arith_term_leq0(term_manager_t *manager, term_t t) {
  rba_buffer_t *b;

  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);
  rba_buffer_add_term(b, manager->terms, t);

  return mk_arith_leq0(manager, b);
}

// t > 0
term_t mk_arith_term_gt0(term_manager_t *manager, term_t t) {
  rba_buffer_t *b;

  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);
  rba_buffer_add_term(b, manager->terms, t);

  return mk_arith_gt0(manager, b);
}

// t < 0
term_t mk_arith_term_lt0(term_manager_t *manager, term_t t) {
  rba_buffer_t *b;

  b = term_manager_get_arith_buffer(manager);
  reset_rba_buffer(b);
  rba_buffer_add_term(b, manager->terms, t);

  return mk_arith_lt0(manager, b);
}


/*
 * Variant: use a term table
 */
// b <= 0  -->  (- b) >= 0
term_t mk_direct_arith_leq0(term_table_t *tbl, rba_buffer_t *b) {
  rba_buffer_negate(b);
  return mk_direct_arith_geq0(tbl, b);
}

// b > 0  -->  not (b <= 0)
term_t mk_direct_arith_gt0(term_table_t *tbl, rba_buffer_t *b) {
  return opposite_term(mk_direct_arith_leq0(tbl, b));
}

// b < 0  -->  not (b >= 0)
term_t mk_direct_arith_lt0(term_table_t *tbl, rba_buffer_t *b) {
  return opposite_term(mk_direct_arith_geq0(tbl, b));
}






/****************
 *  EQUALITIES  *
 ***************/

/*
 * Bitvector equality and disequality
 */
term_t mk_bveq(term_manager_t *manager, term_t t1, term_t t2) {
  return mk_bitvector_eq(manager, t1, t2);
}

term_t mk_bvneq(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_bitvector_eq(manager, t1, t2));
}


/*
 * Generic equality: convert to boolean, arithmetic, or bitvector equality
 */
term_t mk_eq(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;
  term_t aux;

  tbl = manager->terms;

  if (is_boolean_term(tbl, t1)) {
    assert(is_boolean_term(tbl, t2));
    return mk_iff(manager, t1, t2);
  }

  if (is_arithmetic_term(tbl, t1)) {
    assert(is_arithmetic_term(tbl, t2));
    return mk_arith_eq(manager, t1, t2);
  }

  if (is_bitvector_term(tbl, t1)) {
    assert(is_bitvector_term(tbl, t2));
    return mk_bveq(manager, t1, t2);
  }

  // general case
  if (t1 == t2) return true_term;
  if (disequal_terms(tbl, t1, t2)) {
    return false_term;
  }

  // put smaller index on the left
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  return eq_term(tbl, t1, t2);
}


/*
 * Generic disequality.
 *
 * We don't want to return (not mk_eq(manager, t1, t2)) because
 * that could miss some simplifications if t1 and t2 are Boolean.
 */
term_t mk_neq(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;
  term_t aux;

  tbl = manager->terms;

  if (is_boolean_term(tbl, t1)) {
    assert(is_boolean_term(tbl, t2));
    return mk_binary_xor(manager, t1, t2);
  }

  if (is_arithmetic_term(tbl, t1)) {
    assert(is_arithmetic_term(tbl, t2));
    return mk_arith_neq(manager, t1, t2);
  }

  if (is_bitvector_term(tbl, t1)) {
    assert(is_bitvector_term(tbl, t2));
    return mk_bvneq(manager, t1, t2);
  }

  // general case
  if (t1 == t2) return false_term;
  if (disequal_terms(tbl, t1, t2)) {
    return true_term;
  }

  // put smaller index on the left
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  return opposite_term(eq_term(tbl, t1, t2));
}


/*
 * Array disequality:
 * - given two arrays a and b of n terms, build the term
 *   (or (/= a[0] b[0]) ... (/= a[n-1] b[n-1]))
 */
term_t mk_array_neq(term_manager_t *manager, uint32_t n, const term_t a[], const term_t b[]) {
  uint32_t i;
  term_t *aux;

  resize_ivector(&manager->vector0, n);
  aux = manager->vector0.data;

  for (i=0; i<n; i++) {
    aux[i] = mk_neq(manager, a[i], b[i]);
  }
  return mk_or(manager, n, aux);
}


/*
 * Array equality:
 * - given two arrays a and b of n term, build
 *   (and (= a[0] b[0]) ... (= a[n-1] b[n-1])
 */
term_t mk_array_eq(term_manager_t *manager, uint32_t n, const term_t a[], const term_t b[]) {
  return opposite_term(mk_array_neq(manager, n, a, b));
}




/*****************************
 *   GENERIC CONSTRUCTORS    *
 ****************************/

/*
 * When constructing a term of singleton type tau, we return the
 * representative for tau (except for variables).
 */

/*
 * Constant of type tau and index i
 * - tau must be uninterpreted or scalar type
 * - i must be non-negative and smaller than the size of tau
 *   (which matters only if tau is scalar)
 */
term_t mk_constant(term_manager_t *manager, type_t tau, int32_t i) {
  term_t t;

  assert(i >= 0);
  t = constant_term(manager->terms, tau, i);
  if (is_unit_type(manager->types, tau)) {
    store_unit_type_rep(manager->terms, tau, t);
  }

  return t;
}


/*
 * New uninterpreted term of type tau
 * - i.e., this creates a fresh global variable
 */
term_t mk_uterm(term_manager_t *manager, type_t tau) {
  if (is_unit_type(manager->types, tau)) {
    return get_unit_type_rep(manager->terms, tau);
  }

  return new_uninterpreted_term(manager->terms, tau);
}


/*
 * New variable of type tau
 * - this creates a fresh variable (for quantifiers)
 */
term_t mk_variable(term_manager_t *manager, type_t tau) {
  return new_variable(manager->terms, tau);
}



/*
 * Function application:
 * - fun must have arity n
 * - arg = array of n arguments
 * - the argument types much match the domain of f
 *
 * Simplifications if fun is an update term:
 *   ((update f (a_1 ... a_n) v) a_1 ... a_n)   -->  v
 *   ((update f (a_1 ... a_n) v) x_1 ... x_n)   -->  (f x_1 ... x_n)
 *         if x_i must disequal a_i
 *
 */
term_t mk_application(term_manager_t *manager, term_t fun, uint32_t n, const term_t arg[]) {
  term_table_t *tbl;
  type_table_t *types;
  composite_term_t *update;
  type_t tau;

  tbl = manager->terms;
  types = manager->types;

  // singleton function type
  tau = term_type(tbl, fun);
  if (is_unit_type(types, tau)) {
    return get_unit_type_rep(tbl, function_type_range(types, tau));
  }

  while (term_kind(tbl, fun) == UPDATE_TERM) {
    // fun is (update f (a_1 ... a_n) v)
    update = update_term_desc(tbl, fun);
    assert(update->arity == n+2);

    /*
     * update->arg[0] is f
     * update->arg[1] to update->arg[n] = a_1 to a_n
     * update->arg[n+1] is v
     */
    if (equal_term_arrays(n, update->arg + 1, arg)) {
      return update->arg[n+1];
    }

    if (disequal_term_arrays(tbl, n, update->arg + 1, arg)) {
      // ((update f (a_1 ... a_n) v) x_1 ... x_n) ---> (f x_1 ... x_n)
      // repeat simplification if f is an update term again
      fun = update->arg[0];
    } else {
      break;
    }
  }

  return app_term(tbl, fun, n, arg);
}



/*
 * Attempt to simplify (mk-tuple arg[0] .... arg[n-1]):
 * return x if arg[i] = (select i x) for i=0 ... n-1 and x is a tuple term of arity n
 * return NULL_TERM otherwise
 */
static term_t simplify_mk_tuple(term_table_t *tbl, uint32_t n, const term_t arg[]) {
  uint32_t i;
  term_t x, a;

  a = arg[0];
  if (is_neg_term(a) ||
      term_kind(tbl, a) != SELECT_TERM ||
      select_term_index(tbl, a) != 0) {
    return NULL_TERM;
  }

  // arg[0] is (select 0 x)
  x = select_term_arg(tbl, a);
  if (tuple_type_arity(tbl->types, term_type(tbl, x)) != n) {
    // x does not have arity n
    return NULL_TERM;
  }

  for (i = 1; i<n; i++) {
    a = arg[i];
    if (is_neg_term(a) ||
        term_kind(tbl, a) != SELECT_TERM ||
        select_term_index(tbl, a) != i ||
        select_term_arg(tbl, a) != x) {
      // arg[i] is not (select i x)
      return NULL_TERM;
    }
  }

  return x;
}


/*
 * Tuple constructor:
 * - arg = array of n terms
 * - n must be positive and no more than YICES_MAX_ARITY
 *
 * Simplification:
 *   (mk_tuple (select 0 x) ... (select n-1 x)) --> x
 * provided x is a tuple of arity n
 */
term_t mk_tuple(term_manager_t *manager, uint32_t n, const term_t arg[]) {
  term_table_t *tbl;
  term_t x;
  type_t tau;

  tbl = manager->terms;
  x = simplify_mk_tuple(tbl, n, arg);
  if (x == NULL_TERM) {
    // not simplified
    x = tuple_term(tbl, n, arg);

    // check whether x is unique element of its type
    tau = term_type(tbl, x);
    if (is_unit_type(manager->types, tau)) {
      store_unit_type_rep(tbl, tau, x);
    }
  }

  return x;
}


/*
 * Projection: component i of tuple.
 * - tuple must have tuple type
 * - i must be between 0 and the number of components in the tuple
 *   type - 1
 *
 * Simplification: (select i (mk_tuple x_1 ... x_n))  --> x_i
 */
term_t mk_select(term_manager_t *manager, uint32_t index, term_t tuple) {
  term_table_t *tbl;
  type_table_t *types;
  type_t tau;
  term_t x;

  // simplify
  if (term_kind(manager->terms, tuple) == TUPLE_TERM) {
    x = composite_term_arg(manager->terms, tuple, index);
  } else {
    // check for singleton type
    tbl = manager->terms;
    types = manager->types;
    tau = term_type(tbl, tuple);
    tau = tuple_type_component(types, tau, index);

    if (is_unit_type(types, tau)) {
      x = get_unit_type_rep(tbl, tau);
    } else {
      x = select_term(tbl, index, tuple);
    }
  }

  return x;
}


/*
 * Function update: (update f (arg[0] ... arg[n-1]) new_v)
 * - f must have function type and arity n
 * - new_v's type must be a subtype of f's range
 *
 * Simplifications:
 *  (update (update f (a_1 ... a_n) v) (a_1 ... a_n) v') --> (update f (a_1 ... a_n) v')
 *  (update f (a_1 ... a_n) (f a_1 ... a_n)) --> f
 */
term_t mk_update(term_manager_t *manager, term_t fun, uint32_t n, const term_t arg[], term_t new_v) {
  term_table_t *tbl;
  composite_term_t *update, *app;
  type_t tau;

  tbl = manager->terms;

  // singleton function type
  tau = term_type(tbl, fun);
  if (is_unit_type(manager->types, tau)) {
    assert(unit_type_rep(tbl, tau) == fun);
    return fun;
  }

  // try simplification
  while (term_kind(tbl, fun) == UPDATE_TERM) {
    // fun is (update f b_1 ... b_n v)
    update = update_term_desc(tbl, fun);
    assert(update->arity == n+2);

    if (equal_term_arrays(n, update->arg + 1, arg)) {
      // b_1 = a_1, ..., b_n = a_n so
      // (update (update fun b_1 ... b_n v0) a_1 ... a_n new_v)) --> (update fun (a_1 ... a_n) new_v)
      fun = update->arg[0];
    } else {
      break;
    }
  }

  // build (update fun a_1 .. a_n new_v): try second simplification
  if (term_kind(tbl, new_v) == APP_TERM) {
    app = app_term_desc(tbl, new_v);
    if (app->arity == n+1 && app->arg[0] == fun &&
        equal_term_arrays(n, app->arg + 1, arg)) {
      // new_v is (apply fun a_1 ... a_n)
      return fun;
    }
  }

  return update_term(tbl, fun, n, arg, new_v);
}



/*
 * Distinct: all terms arg[0] ... arg[n-1] must have compatible types
 * - n must be positive and no more than YICES_MAX_ARITY
 *
 * (distinct t1 ... t_n):
 *
 * if n == 1 --> true
 * if n == 2 --> (diseq t1 t2)
 * if t_i and t_j are equal --> false
 * if all are disequal --> true
 *
 * More simplifications uses type information,
 *  (distinct f g h) --> false if f g h are boolean.
 */
term_t mk_distinct(term_manager_t *manager, uint32_t n, term_t arg[]) {
  uint32_t i;
  type_t tau;

  if (n == 1) {
    return true_term;
  }

  if (n == 2) {
    return mk_neq(manager, arg[0], arg[1]);
  }

  // check for finite types
  tau = term_type(manager->terms, arg[0]);
  if (type_card(manager->types, tau) < n && type_card_is_exact(manager->types, tau)) {
    // card exact implies that tau is finite (and small)
    return false_term;
  }


  // check if two of the terms are equal
  int_array_sort(arg, n);
  for (i=1; i<n; i++) {
    if (arg[i] == arg[i-1]) {
      return false_term;
    }
  }

  // WARNING: THIS CAN BE EXPENSIVE
  if (pairwise_disequal_terms(manager->terms, n, arg)) {
    return true_term;
  }

  return distinct_term(manager->terms, n, arg);
}


/*
 * (tuple-update tuple index new_v) is (tuple with component i set to new_v)
 *
 * If new_v is (select t i) then
 *  (tuple-update t i v) is t
 *
 * If tuple is (mk-tuple x_0 ... x_i ... x_n-1) then
 *  (tuple-update t i v) is (mk-tuple x_0 ... v ... x_n-1)
 *
 * Otherwise,
 *  (tuple-update t i v) is (mk-tuple (select t 0) ... v  ... (select t n-1))
 *
 */
static term_t mk_tuple_aux(term_manager_t *manager, term_t tuple, uint32_t n, uint32_t i, term_t v) {
  term_table_t *tbl;
  composite_term_t *desc;
  term_t *a;
  term_t t;
  uint32_t j;

  tbl = manager->terms;

  if (is_pos_term(v) && term_kind(tbl, v) == SELECT_TERM &&
      select_term_arg(tbl, v) == tuple && select_term_index(tbl, v) == i) {
    return tuple;
  }

  // use vector0 as buffer:
  resize_ivector(&manager->vector0, n);
  a = manager->vector0.data;

  if (term_kind(tbl, tuple) == TUPLE_TERM) {
    desc = tuple_term_desc(tbl, tuple);
    for (j=0; j<n; j++) {
      if (i == j) {
        a[j] = v;
      } else {
        a[j] = desc->arg[j];
      }
    }
  } else {
    for (j=0; j<n; j++) {
      if (i == j) {
        a[j] = v;
      } else {
        a[j] = select_term(tbl, j, tuple);
      }
    }
  }

  t = tuple_term(tbl, n, a);

  // cleanup
  ivector_reset(&manager->vector0);

  return t;
}


/*
 * Tuple update: replace component i of tuple by new_v
 */
term_t mk_tuple_update(term_manager_t *manager, term_t tuple, uint32_t index, term_t new_v) {
  uint32_t n;
  type_t tau;

  // singleton type
  tau = term_type(manager->terms, tuple);
  if (is_unit_type(manager->types, tau)) {
    assert(unit_type_rep(manager->terms, tau) == tuple);
    return tuple;
  }

  n = tuple_type_arity(manager->types, tau);
  return mk_tuple_aux(manager, tuple, n, index, new_v);
}



/*
 * Quantifiers:
 * - n = number of variables (n must be positive and no more than YICES_MAX_VAR)
 * - all variables v[0 ... n-1] must be distinct
 * - body must be a Boolean term
 *
 * Simplification
 *  (forall (x_1::t_1 ... x_n::t_n) true) --> true
 *  (forall (x_1::t_1 ... x_n::t_n) false) --> false (types are nonempty)
 *
 *  (exists (x_1::t_1 ... x_n::t_n) true) --> true
 *  (exists (x_1::t_1 ... x_n::t_n) false) --> false (types are nonempty)
 */
term_t mk_forall(term_manager_t *manager, uint32_t n, const term_t var[], term_t body) {
  if (body == true_term) return body;
  if (body == false_term) return body;

  return forall_term(manager->terms, n, var, body);
}

term_t mk_exists(term_manager_t *manager, uint32_t n, const term_t var[], term_t body) {
  if (body == true_term) return body;
  if (body == false_term) return body;

  // (not (forall ... (not body))
  return opposite_term(forall_term(manager->terms, n, var, opposite_term(body)));
}



/*
 * Lambda term:
 * - n = number of variables
 * - var[0 .. n-1] = variables (must all be distinct)
 *
 * Simplification:
 *   (lambda (x_1::t_1 ... x_n::t_n) (f x_1 ... x_n)) --> f
 *
 * provided f has type [t_1 ... t_n --> sigma]
 */

// check whether var[0 ... n-1] and arg[0 ... n-1] are equal
static bool equal_arrays(const term_t var[], const term_t arg[], uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (var[i] != arg[i]) {
      return false;
    }
  }

  return true;
}

// check whether the domain of f matches the variable types
static bool same_domain(term_table_t *table, term_t f, const term_t var[], uint32_t n) {
  function_type_t *desc;
  type_t tau;
  uint32_t i;

  tau = term_type(table, f);
  desc = function_type_desc(table->types, tau);
  assert(desc->ndom == n);

  for (i=0; i<n; i++) {
    if (desc->domain[i] != term_type(table, var[i])) {
      return false;
    }
  }

  return true;
}

term_t mk_lambda(term_manager_t *manager, uint32_t n, const term_t var[], term_t body) {
  term_table_t *tbl;
  composite_term_t *d;
  term_t f;

  assert(0 < n && n <= YICES_MAX_ARITY);

  tbl = manager->terms;
  if (is_pos_term(body) && term_kind(tbl, body) == APP_TERM) {
    d = app_term_desc(tbl, body);
    if (d->arity == n+1 && equal_arrays(var, d->arg + 1, n)) {
      f = d->arg[0];
      if (same_domain(tbl, f, var, n)) {
        return f;
      }
    }
  }

  return lambda_term(manager->terms, n, var, body);
}




/*************************
 *  BITVECTOR CONSTANTS  *
 ************************/

/*
 * Convert b to a bitvector constant
 * - normalize b first
 * - b->bitsize must be positive and no more than YICES_MAX_BVSIZE
 * - depending on b->bitsize, this either builds a bv64 constant
 *   or a wide bvconst term (more than 64 bits)
 */
term_t mk_bv_constant(term_manager_t *manager, bvconstant_t *b) {
  uint32_t n;
  uint64_t x;
  term_t t;

  assert(b->bitsize > 0);

  n = b->bitsize;
  bvconst_normalize(b->data, n); // reduce modulo 2^n

  if (n <= 64) {
    if (n <= 32) {
      x = bvconst_get32(b->data);
    } else {
      x = bvconst_get64(b->data);
    }
    t = bv64_constant(manager->terms, n, x);
  } else {
    t = bvconst_term(manager->terms, n, b->data);
  }

  return t;
}



/**************************
 *  CONVERT BITS TO TERMS  *
 *************************/

/*
 * A bvlogic buffer stores an array of bits in manager->nodes.
 * Function bvlogic_buffer_get_bvarray requires converting bits
 * back to Boolean terms.
 *
 * The nodes data structure is defined in bit_expr.h
 */

/*
 * Recursive function: return the term mapped to node x
 * - compute it if needed then store the result in manager->nodes->map[x]
 */
static term_t map_node_to_term(term_manager_t *manager, node_t x);

/*
 * Get the term mapped to bit b. If node_of(b) is mapped to t then
 * - if b has positive polarity, map_of(b) = t
 * - if b has negative polarity, map_of(b) = not t
 */
static inline term_t map_bit_to_term(term_manager_t *manager, bit_t b) {
  return map_node_to_term(manager, node_of_bit(b)) ^ polarity_of(b);
}



/*
 * Given two bits b1 = c[0] and b2 = c[1], convert (or b1 b2) to a term
 */
static term_t make_or2(term_manager_t *manager, bit_t *c) {
  term_t x, y;

  x = map_bit_to_term(manager, c[0]);
  y = map_bit_to_term(manager, c[1]);

  assert(is_boolean_term(manager->terms, x) &&
	 is_boolean_term(manager->terms, y));

  return mk_binary_or(manager, x, y);
}


/*
 * Same thing for (xor c[0] c[1])
 */
static term_t make_xor2(term_manager_t *manager, bit_t *c) {
  term_t x, y;

  x = map_bit_to_term(manager, c[0]);
  y = map_bit_to_term(manager, c[1]);

  assert(is_boolean_term(manager->terms, x) &&
	 is_boolean_term(manager->terms, y));

  return mk_binary_xor(manager, x, y);
}



/*
 * Recursive function: return the term mapped to node x
 * - compute it if needed then store the result in nodes->map[x]
 */
static term_t map_node_to_term(term_manager_t *manager, node_t x) {
  node_table_t *nodes;
  term_t t;

  nodes = manager->nodes;
  assert(nodes != NULL);

  t = map_of_node(nodes, x);
  if (t < 0) {
    assert(t == -1);

    switch (node_kind(nodes, x)) {
    case CONSTANT_NODE:
      // x is true
      t = true_term;
      break;

    case VARIABLE_NODE:
      // x is (var t) for a boolean term t
      t = var_of_node(nodes, x);
      break;

    case SELECT_NODE:
      // x is (select i u) for a bitvector term u
      t = mk_bitextract(manager, var_of_select_node(nodes, x), index_of_select_node(nodes, x));
      break;

    case OR_NODE:
      t = make_or2(manager, children_of_node(nodes, x));
      break;

    case XOR_NODE:
      t = make_xor2(manager, children_of_node(nodes, x));
      break;

    default:
      assert(false);
      abort();
      break;
    }

    assert(is_boolean_term(manager->terms, t));
    set_map_of_node(nodes, x, t);
  }

  return t;
}





/*******************
 *  BVLOGIC TERMS  *
 ******************/

/*
 * Convert buffer b to a bv_constant term
 * - side effect: use bv0
 */
static term_t bvlogic_buffer_get_bvconst(term_manager_t *manager, bvlogic_buffer_t *b) {
  bvconstant_t *bv;

  assert(bvlogic_buffer_is_constant(b));

  bv = &manager->bv0;
  bvlogic_buffer_get_constant(b, bv);
  return bvconst_term(manager->terms, bv->bitsize, bv->data);
}


/*
 * Convert buffer b to a bv-array term
 */
static term_t bvlogic_buffer_get_bvarray(term_manager_t *manager, bvlogic_buffer_t *b) {
  uint32_t i, n;

  assert(b->nodes == manager->nodes && manager->nodes != NULL);

  // translate each bit of b into a boolean term
  // we store the translation in b->bit
  n = b->bitsize;
  for (i=0; i<n; i++) {
    b->bit[i] = map_bit_to_term(manager, b->bit[i]);
  }

  // build the term (bvarray b->bit[0] ... b->bit[n-1])
  return bvarray_term(manager->terms, n, b->bit);
}


/*
 * Convert b to a term then reset b.
 * - b must not be empty.
 * - build a bitvector constant if possible
 * - if b is of the form (select 0 t) ... (select k t) and t has bitsize (k+1)
 *   then return t
 * - otherwise build a bitarray term
 */
term_t mk_bvlogic_term(term_manager_t *manager, bvlogic_buffer_t *b) {
  term_t t;
  uint32_t n;

  n = b->bitsize;
  assert(0 < n && n <= YICES_MAX_BVSIZE);

  if (bvlogic_buffer_is_constant(b)) {
    if (n <= 64) {
      // small constant
      t = bv64_constant(manager->terms, n, bvlogic_buffer_get_constant64(b));
    } else {
      // wide constant
      t = bvlogic_buffer_get_bvconst(manager, b);
    }

  } else {
    t = bvlogic_buffer_get_var(b);
    if (t < 0 || term_bitsize(manager->terms, t) != n) {
      // not a variable
      t = bvlogic_buffer_get_bvarray(manager, b);
    }
  }

  assert(is_bitvector_term(manager->terms, t) &&
         term_bitsize(manager->terms, t) == n);

  bvlogic_buffer_clear(b);

  return t;
}



/***************************
 *  BITVECTOR POLYNOMIALS  *
 **************************/

/*
 * Store array [false_term, ..., false_term] into vector v
 */
static void bvarray_set_zero_bv(ivector_t *v, uint32_t n) {
  uint32_t i;

  assert(0 < n && n <= YICES_MAX_BVSIZE);
  resize_ivector(v, n);
  for (i=0; i<n; i++) {
    v->data[i] = false_term;
  }
}

/*
 * Store constant c into vector v
 * - n = number of bits in c
 */
static void bvarray_copy_constant(ivector_t *v, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(0 < n && n <= YICES_MAX_BVSIZE);
  resize_ivector(v, n);
  for (i=0; i<n; i++) {
    v->data[i] = bool2term(bvconst_tst_bit(c, i));
  }
}

/*
 * Same thing for a small constant c
 */
static void bvarray_copy_constant64(ivector_t *v, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(0 < n && n <= 64);
  resize_ivector(v, n);
  for (i=0; i<n; i++) {
    v->data[i] = bool2term(tst_bit64(c, i));
  }
}


/*
 * Check whether v + a * x can be converted to (v | (x << k))  for some k
 * - a must be an array of n boolean terms
 * - v must contain a bitvector constant (represented as an array of
 *   integers, each equal to true_term or false_term)
 * - return true if that can be done and update v to (v | (x << k))
 * - otherwise, return false and keep v unchanged
 */
static bool bvarray_check_addmul(ivector_t *v, uint32_t n, uint32_t *c, term_t *a) {
  uint32_t i, w;
  int32_t k;

  w = (n + 31) >> 5; // number of words in c
  if (bvconst_is_zero(c, w)) {
    return true;
  }

  k = bvconst_is_power_of_two(c, w);
  if (k < 0) {
    return false;
  }

  // c is 2^k; check whether v + (a << k) is equal to v | (a << k)
  assert(0 <= k && k < n);
  for (i=k; i<n; i++) {
    if (v->data[i] != false_term && a[i-k] != false_term) {
      return false;
    }
  }

  // update v here
  for (i=k; i<n; i++) {
    if (a[i-k] != false_term) {
      assert(v->data[i] == false_term);
      v->data[i] = a[i-k];
    }
  }

  return true;
}


/*
 * Same thing for c stored as a small constant (64 bits at most)
 */
static bool bvarray_check_addmul64(ivector_t *v, uint32_t n, uint64_t c, term_t *a) {
  uint32_t i, k;

  assert(0 < n && n <= 64 && c == norm64(c, n));

  if (c == 0) {
    return true;
  }

  k = ctz64(c); // k = index of the rightmost 1 in c
  assert(0 <= k && k <= 63);
  if (c != (((uint64_t) 1) << k)) {
    // c != 2^k
    return false;
  }

  // c is 2^k check whether v + (a << k) is equal to v | (a << k)
  assert(0 <= k && k < n);
  for (i=k; i<n; i++) {
    if (v->data[i] != false_term && a[i-k] != false_term) {
      return false;
    }
  }

  // update v here
  for (i=k; i<n; i++) {
    if (a[i-k] != false_term) {
      assert(v->data[i] == false_term);
      v->data[i] = a[i-k];
    }
  }

  return true;
}




/*
 * Check whether power product r is equal to a bit-array term t
 * - if so return t's descriptor, otherwise return NULL
 */
static composite_term_t *pprod_get_bvarray(term_table_t *tbl, pprod_t *r) {
  composite_term_t *bv;
  term_t t;

  bv = NULL;
  if (pp_is_var(r)) {
    t = var_of_pp(r);
    if (term_kind(tbl, t) == BV_ARRAY) {
      bv = composite_for_idx(tbl, index_of(t));
    }
  }

  return bv;
}


/*
 * Attempt to convert a bvarith buffer to a bv-array term
 * - b = bvarith buffer (list of monomials)
 * - return NULL_TERM if the conversion fails
 * - return a term t if the conversion succeeds.
 * - side effect: use vector0
 */
static term_t convert_bvarith_to_bvarray(term_manager_t *manager, bvarith_buffer_t *b) {
  composite_term_t *bv;
  bvmlist_t *m;
  ivector_t *v;
  uint32_t n;

  v = &manager->vector0;

  n = b->bitsize;
  m = b->list; // first monomial
  if (m->prod == empty_pp) {
    // copy constant into v
    bvarray_copy_constant(v, n, m->coeff);
    m = m->next;
  } else {
    // initialze v to 0b0000..0
    bvarray_set_zero_bv(v, n);
  }

  while (m->next != NULL) {
    bv = pprod_get_bvarray(manager->terms, m->prod);
    if (bv == NULL) return NULL_TERM;

    assert(bv->arity == n);

    // try to convert coeff * v into shift + bitwise or
    if (! bvarray_check_addmul(v, n, m->coeff, bv->arg)) {
      return NULL_TERM;  // conversion failed
    }
    m = m->next;
  }

  // Success: construct a bit array from v
  return bvarray_term(manager->terms, n, v->data);
}


/*
 * Attempt to convert a bvarith64 buffer to a bv-array term
 * - b = bvarith buffer (list of monomials)
 * - return NULL_TERM if the conversion fails
 * - return a term t if the conversion succeeds.
 * - side effect: use vector0
 */
static term_t convert_bvarith64_to_bvarray(term_manager_t *manager, bvarith64_buffer_t *b) {
  composite_term_t *bv;
  bvmlist64_t *m;
  ivector_t *v;
  uint32_t n;

  v = &manager->vector0;

  n = b->bitsize;
  m = b->list; // first monomial
  if (m->prod == empty_pp) {
    // copy constant into vector0
    bvarray_copy_constant64(v, n, m->coeff);
    m = m->next;
  } else {
    // initialze vector0 to 0
    bvarray_set_zero_bv(v, n);
  }

  while (m->next != NULL) {
    bv = pprod_get_bvarray(manager->terms, m->prod);
    if (bv == NULL) return NULL_TERM;

    assert(bv->arity == n);

    // try to convert coeff * v into shift + bitwise or
    if (! bvarray_check_addmul64(v, n, m->coeff, bv->arg)) {
      return NULL_TERM;  // conversion failed
    }
    m = m->next;
  }

  // Success: construct a bit array from v
  return bvarray_term(manager->terms, n, v->data);
}


/*
 * Constant bitvector with all bits 0
 * - n = bitsize (must satisfy 0 < n && n <= YICES_MAX_BVSIZE)
 * - side effect: modify bv0
 */
static term_t make_zero_bv(term_manager_t *manager, uint32_t n) {
  bvconstant_t *bv;

  assert(0 < n && n <= YICES_MAX_BVSIZE);

  bv = &manager->bv0;

  if (n > 64) {
    bvconstant_set_all_zero(bv, n);
    return bvconst_term(manager->terms, bv->bitsize, bv->data);
  } else {
    return bv64_constant(manager->terms, n, 0);
  }
}


/*
 * Convert a polynomial buffer to a bitvector terms:
 * - b must use the same pprod as manager (i.e., b->ptbl = manager->pprods)
 * - b may be equal to manager->bvarith_buffer
 * - side effect: b is reset
 *
 * This normalizes b first then check for the following:
 * 1) b reduced to a single variable x: return x
 * 2) b reduced to a power product pp: return pp
 * 3) b is constant, return a BV64_CONSTANT or BV_CONSTANT term
 * 4) b can be converted to a BV_ARRAY term (by converting + and *
 *    to bitwise or and shift): return the BV_ARRAY
 *
 * Otherwise, build a bit-vector polynomial.
 */
term_t mk_bvarith_term(term_manager_t *manager, bvarith_buffer_t *b) {
  bvmlist_t *m;
  pprod_t *r;
  uint32_t n, p, k;
  term_t t;

  assert(b->bitsize > 0);

  bvarith_buffer_normalize(b);

  n = b->bitsize;
  k = (n + 31) >> 5;
  p = b->nterms;
  if (p == 0) {
    // zero
    t = make_zero_bv(manager, n);
    goto done;
  }

  if (p == 1) {
    m = b->list; // unique monomial of b
    r = m->prod;
    if (r == empty_pp) {
      // constant
      t = bvconst_term(manager->terms, n, m->coeff);
      goto done;
    }
    if (bvconst_is_one(m->coeff, k)) {
      // power product
      t = pp_is_var(r) ? var_of_pp(r) : pprod_term(manager->terms, r);
      goto done;
    }
  }

  // try to convert to a bvarray term
  t = convert_bvarith_to_bvarray(manager, b);
  if (t == NULL_TERM) {
    // conversion failed: build a bvpoly
    t = bv_poly(manager->terms, b);
  }

 done:
  bvarith_buffer_prepare(b, 32); // reset b, any positive n would do
  assert(is_bitvector_term(manager->terms, t) &&
         term_bitsize(manager->terms, t) == n);

  return t;
}



/*
 * Normalize b then convert it to a term and reset b
 */
term_t mk_bvarith64_term(term_manager_t *manager, bvarith64_buffer_t *b) {
  bvmlist64_t *m;
  pprod_t *r;
  uint32_t n, p;
  term_t t;

  assert(b->bitsize > 0);

  bvarith64_buffer_normalize(b);

  n = b->bitsize;
  p = b->nterms;
  if (p == 0) {
    // zero
    t = make_zero_bv(manager, n);
    goto done;
  }

  if (p == 1) {
    m = b->list; // unique monomial of b
    r = m->prod;
    if (r == empty_pp) {
      // constant
      t = bv64_constant(manager->terms, n, m->coeff);
      goto done;
    }
    if (m->coeff == 1) {
      // power product
      t = pp_is_var(r) ? var_of_pp(r) : pprod_term(manager->terms, r);
      goto done;
    }
  }

  // try to convert to a bvarray term
  t = convert_bvarith64_to_bvarray(manager, b);
  if (t == NULL_TERM) {
    // conversion failed: build a bvpoly
    t = bv64_poly(manager->terms, b);
  }

 done:
  bvarith64_buffer_prepare(b, 32); // reset b, any positive n would do
  assert(is_bitvector_term(manager->terms, t) &&
         term_bitsize(manager->terms, t) == n);

  return t;
}



/***************
 *  BIT ARRAY  *
 **************/

/*
 * Bit array
 * - a must be an array of n boolean terms
 * - n must be positive and no more than YICES_MAX_BVSIZE
 */
term_t mk_bvarray(term_manager_t *manager, uint32_t n, const term_t *a) {
  bvlogic_buffer_t *b;

  assert(0 < n && n <= YICES_MAX_BVSIZE);

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term_array(b, manager->terms, n, a);
  return mk_bvlogic_term(manager, b);
}


/**********************
 *  BITVECTOR  SHIFT  *
 *********************/

/*
 * All shift operators takes two bit-vector arguments of the same size.
 * The first argument is shifted. The second argument is the shift amount.
 * - bvshl t1 t2: shift left, padding with 0
 * - bvlshr t1 t2: logical shift right (padding with 0)
 * - bvashr t1 t2: arithmetic shift right (copy the sign bit)
 *
 * We check whether t2 is a bit-vector constant and convert to
 * constant bit-shifts in such cases.
 */


/*
 * SHIFT LEFT
 */

// shift amount given by a small bitvector constant
static term_t mk_bvshl_const64(term_manager_t *manager, term_t t1, bvconst64_term_t *c) {
  bvlogic_buffer_t *b;

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, manager->terms, t1);
  bvlogic_buffer_shl_constant64(b, c->bitsize, c->value);

  return mk_bvlogic_term(manager, b);
}

// shift amount given by a large bitvector constant
static term_t mk_bvshl_const(term_manager_t *manager, term_t t1, bvconst_term_t *c) {
  bvlogic_buffer_t *b;

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, manager->terms, t1);
  bvlogic_buffer_shl_constant(b, c->bitsize, c->data);

  return mk_bvlogic_term(manager, b);
}

// special case: if t1 is 0b000...0 then (bvshl t1 t2) = t2 for any t2
static bool term_is_bvzero(term_table_t *tbl, term_t t1) {
  bvconst64_term_t *u;
  bvconst_term_t *v;
  uint32_t k;

  switch (term_kind(tbl, t1)) {
  case BV64_CONSTANT:
    u = bvconst64_term_desc(tbl, t1);
    assert(u->value == norm64(u->value, u->bitsize));
    return u->value == 0;

  case BV_CONSTANT:
    v = bvconst_term_desc(tbl, t1);
    k = (v->bitsize + 31) >> 5; // number of words in v
    return bvconst_is_zero(v->data, k);

  default:
    return false;
  }
}


term_t mk_bvshl(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    return mk_bvshl_const64(manager, t1, bvconst64_term_desc(tbl, t2));

  case BV_CONSTANT:
    return mk_bvshl_const(manager, t1, bvconst_term_desc(tbl, t2));

  default:
    if (term_is_bvzero(tbl, t1)) {
      return t1;
    } else {
      return bvshl_term(tbl, t1, t2);
    }
  }
}



/*
 * LOGICAL SHIFT RIGHT
 */

// shift amount given by a small bitvector constant
static term_t mk_bvlshr_const64(term_manager_t *manager, term_t t1, bvconst64_term_t *c) {
  bvlogic_buffer_t *b;

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, manager->terms, t1);
  bvlogic_buffer_lshr_constant64(b, c->bitsize, c->value);

  return mk_bvlogic_term(manager, b);
}

// logical shift right: amount given by a large bitvector constant
static term_t mk_bvlshr_const(term_manager_t *manager, term_t t1, bvconst_term_t *c) {
  bvlogic_buffer_t *b;

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, manager->terms, t1);
  bvlogic_buffer_lshr_constant(b, c->bitsize, c->data);

  return mk_bvlogic_term(manager, b);
}


term_t mk_bvlshr(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    return mk_bvlshr_const64(manager, t1, bvconst64_term_desc(tbl, t2));

  case BV_CONSTANT:
    return mk_bvlshr_const(manager, t1, bvconst_term_desc(tbl, t2));

  default:
    // as above: if t1 is zero, then shifting does not change it
    if (term_is_bvzero(tbl, t1)) {
      return t1;
    } else {
      return bvlshr_term(tbl, t1, t2);
    }
  }
}


/*
 * ARITHMETIC SHIFT RIGHT
 */

// shift amount given by a small bitvector constant
static term_t mk_bvashr_const64(term_manager_t *manager, term_t t1, bvconst64_term_t *c) {
  bvlogic_buffer_t *b;

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, manager->terms, t1);
  bvlogic_buffer_ashr_constant64(b, c->bitsize, c->value);

  return mk_bvlogic_term(manager, b);
}

// shift amount given by a large bitvector constant
static term_t mk_bvashr_const(term_manager_t *manager, term_t t1, bvconst_term_t *c) {
  bvlogic_buffer_t *b;

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, manager->terms, t1);
  bvlogic_buffer_ashr_constant(b, c->bitsize, c->data);

  return mk_bvlogic_term(manager, b);
}

// special case: if t1 is 0b00...00 or 0b11...11 then arithmetic shift
// leaves t1 unchanged (whatever t2)
static bool term_is_bvashr_invariant(term_table_t *tbl, term_t t1) {
  bvconst64_term_t *u;
  bvconst_term_t *v;
  uint32_t k;

  switch (term_kind(tbl, t1)) {
  case BV64_CONSTANT:
    u = bvconst64_term_desc(tbl, t1);
    assert(u->value == norm64(u->value, u->bitsize));
    return u->value == 0 || bvconst64_is_minus_one(u->value, u->bitsize);

  case BV_CONSTANT:
    v = bvconst_term_desc(tbl, t1);
    k = (v->bitsize + 31) >> 5; // number of words in v
    return bvconst_is_zero(v->data, k) || bvconst_is_minus_one(v->data, v->bitsize);

  default:
    return false;
  }

}


term_t mk_bvashr(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    return mk_bvashr_const64(manager, t1, bvconst64_term_desc(tbl, t2));

  case BV_CONSTANT:
    return mk_bvashr_const(manager, t1, bvconst_term_desc(tbl, t2));

  default:
    if (term_is_bvashr_invariant(tbl, t1)) {
      return t1;
    } else {
      return bvashr_term(tbl, t1, t2);
    }
  }
}



/************************
 *  BITVECTOR DIVISION  *
 ***********************/

/*
 * All division/remainder constructors are binary operators with two
 * bitvector arguments of the same size.
 * - bvdiv: quotient in unsigned division
 * - bvrem: remainder in unsigned division
 * - bvsdiv: quotient in signed division (rounding toward 0)
 * - bvsrem: remainder in signed division
 * - bvsmod: remainder in floor division (signed division, rounding toward -infinity)
 *
 * We simplify if the two arguments are constants.
 *
 * TODO: We could convert division/remainder when t2 is a constant powers of two
 * to shift and bit masking operations?
 */


/*
 * Check whether b is a power of 2.
 * - if so return the k such such b = 2^k
 * - otherwise, return -1
 */
static int32_t bvconst64_term_is_power_of_two(bvconst64_term_t *b) {
  uint32_t k;

  if (b->value != 0) {
    k = ctz64(b->value);
    assert(0 <= k && k < b->bitsize && b->bitsize <= 64);
    if (b->value == ((uint64_t) 1) << k) {
      return k;
    }
  }
  return -1;
}

static int32_t bvconst_term_is_power_of_two(bvconst_term_t *b) {
  uint32_t w;

  w = (b->bitsize + 31) >> 5; // number of words in b->data
  return bvconst_is_power_of_two(b->data, w);
}


/*
 * UNSIGNED DIVISION: QUOTIENT
 */
static term_t bvdiv_const64(term_manager_t *manager, bvconst64_term_t *a, bvconst64_term_t *b) {
  uint64_t x;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize);
  x = bvconst64_udiv2z(a->value, b->value, n);
  assert(x == norm64(x, n));

  return bv64_constant(manager->terms, n, x);
}


static term_t bvdiv_const(term_manager_t *manager, bvconst_term_t *a, bvconst_term_t *b) {
  bvconstant_t *bv;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize && n > 64);

  bv = &manager->bv0;

  bvconstant_set_bitsize(bv, n);
  bvconst_udiv2z(bv->data, n, a->data, b->data);
  bvconst_normalize(bv->data, n);

  return bvconst_term(manager->terms, n, bv->data);
}


// divide t1 by 2^k
static term_t bvdiv_power(term_manager_t *manager, term_t t1, uint32_t k) {
  bvlogic_buffer_t *b;

  if (k == 0) return t1;

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_term(b, manager->terms, t1);
  bvlogic_buffer_shift_right0(b, k);

  return mk_bvlogic_term(manager, b);
}


term_t mk_bvdiv(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;
  int32_t k;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    if (term_kind(tbl, t1) == BV64_CONSTANT) {
      return bvdiv_const64(manager, bvconst64_term_desc(tbl, t1), bvconst64_term_desc(tbl, t2));
    }
    k = bvconst64_term_is_power_of_two(bvconst64_term_desc(tbl, t2));
    if (k >= 0) {
      return bvdiv_power(manager, t1, k);
    }
    break;

  case BV_CONSTANT:
    if (term_kind(tbl, t1) == BV_CONSTANT) {
      return bvdiv_const(manager, bvconst_term_desc(tbl, t1), bvconst_term_desc(tbl, t2));
    }
    k = bvconst_term_is_power_of_two(bvconst_term_desc(tbl, t2));
    if (k >= 0) {
      return bvdiv_power(manager, t1, k);
    }
    break;

  default:
    break;
  }

  return bvdiv_term(tbl, t1, t2);
}


/*
 * UNSIGNED DIVISION: REMAINDER
 */
static term_t bvrem_const64(term_manager_t *manager, bvconst64_term_t *a, bvconst64_term_t *b) {
  uint64_t x;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize);
  x = bvconst64_urem2z(a->value, b->value, n);
  assert(x == norm64(x, n));

  return bv64_constant(manager->terms, n, x);
}

static term_t bvrem_const(term_manager_t *manager, bvconst_term_t *a, bvconst_term_t *b) {
  bvconstant_t *bv;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize && n > 64);

  bv = &manager->bv0;

  bvconstant_set_bitsize(bv, n);
  bvconst_urem2z(bv->data, n, a->data, b->data);
  bvconst_normalize(bv->data, n);

  return bvconst_term(manager->terms, n, bv->data);
}

// remainder of t1/2^k
static term_t bvrem_power(term_manager_t *manager, term_t t1, uint32_t k) {
  bvlogic_buffer_t *b;
  uint32_t n;

  n = term_bitsize(manager->terms, t1);
  assert(0 <= k && k < n);

  b = term_manager_get_bvlogic_buffer(manager);
  bvlogic_buffer_set_low_mask(b, k, n);
  bvlogic_buffer_and_term(b, manager->terms, t1);

  return mk_bvlogic_term(manager, b);
}


term_t mk_bvrem(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;
  int32_t k;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    if (term_kind(tbl, t1) == BV64_CONSTANT) {
      return bvrem_const64(manager, bvconst64_term_desc(tbl, t1), bvconst64_term_desc(tbl, t2));
    }
    k = bvconst64_term_is_power_of_two(bvconst64_term_desc(tbl, t2));
    if (k >= 0) {
      return bvrem_power(manager, t1, k);
    }
    break;

  case BV_CONSTANT:
    if (term_kind(tbl, t1) == BV_CONSTANT) {
      return bvrem_const(manager, bvconst_term_desc(tbl, t1), bvconst_term_desc(tbl, t2));
    }
    k = bvconst_term_is_power_of_two(bvconst_term_desc(tbl, t2));
    if (k >= 0) {
      return bvrem_power(manager, t1, k);
    }
    break;

  default:
    break;
  }

  return bvrem_term(tbl, t1, t2);
}


/*
 * SIGNED DIVISION: QUOTIENT
 */
static term_t bvsdiv_const64(term_manager_t *manager, bvconst64_term_t *a, bvconst64_term_t *b) {
  uint64_t x;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize);
  x = bvconst64_sdiv2z(a->value, b->value, n);
  assert(x == norm64(x, n));

  return bv64_constant(manager->terms, n, x);
}

static term_t bvsdiv_const(term_manager_t *manager, bvconst_term_t *a, bvconst_term_t *b) {
  bvconstant_t *bv;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize && n > 64);

  bv = &manager->bv0;

  bvconstant_set_bitsize(bv, n);
  bvconst_sdiv2z(bv->data, n, a->data, b->data);
  bvconst_normalize(bv->data, n);

  return bvconst_term(manager->terms, n, bv->data);
}

term_t mk_bvsdiv(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    if (term_kind(tbl, t1) == BV64_CONSTANT) {
      return bvsdiv_const64(manager, bvconst64_term_desc(tbl, t1), bvconst64_term_desc(tbl, t2));
    }
    break;

  case BV_CONSTANT:
    if (term_kind(tbl, t1) == BV_CONSTANT) {
      return bvsdiv_const(manager, bvconst_term_desc(tbl, t1), bvconst_term_desc(tbl, t2));
    }
    break;

  default:
    break;
  }

  return bvsdiv_term(tbl, t1, t2);
}


/*
 * SIGNED DIVISION: REMAINDER (ROUNDING TO 0)
 */
static term_t bvsrem_const64(term_manager_t *manager, bvconst64_term_t *a, bvconst64_term_t *b) {
  uint64_t x;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize);
  x = bvconst64_srem2z(a->value, b->value, n);
  assert(x == norm64(x, n));

  return bv64_constant(manager->terms, n, x);
}

static term_t bvsrem_const(term_manager_t *manager, bvconst_term_t *a, bvconst_term_t *b) {
  bvconstant_t *bv;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize && n > 64);

  bv = &manager->bv0;

  bvconstant_set_bitsize(bv, n);
  bvconst_srem2z(bv->data, n, a->data, b->data);
  bvconst_normalize(bv->data, n);

  return bvconst_term(manager->terms, n, bv->data);
}

term_t mk_bvsrem(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    if (term_kind(tbl, t1) == BV64_CONSTANT) {
      return bvsrem_const64(manager, bvconst64_term_desc(tbl, t1), bvconst64_term_desc(tbl, t2));
    }
    break;

  case BV_CONSTANT:
    if (term_kind(tbl, t1) == BV_CONSTANT) {
      return bvsrem_const(manager, bvconst_term_desc(tbl, t1), bvconst_term_desc(tbl, t2));
    }
    break;

  default:
    break;
  }

  return bvsrem_term(tbl, t1, t2);
}


/*
 * FLOOR DIVISION: REMAINDER (ROUNDING TO - INFINITY)
 */
static term_t bvsmod_const64(term_manager_t *manager, bvconst64_term_t *a, bvconst64_term_t *b) {
  uint64_t x;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize);
  x = bvconst64_smod2z(a->value, b->value, n);
  assert(x == norm64(x, n));

  return bv64_constant(manager->terms, n, x);
}

static term_t bvsmod_const(term_manager_t *manager, bvconst_term_t *a, bvconst_term_t *b) {
  bvconstant_t *bv;
  uint32_t n;

  n = a->bitsize;
  assert(n == b->bitsize && n > 64);

  bv = &manager->bv0;

  bvconstant_set_bitsize(bv, n);
  bvconst_smod2z(bv->data, n, a->data, b->data);
  bvconst_normalize(bv->data, n);

  return bvconst_term(manager->terms, n, bv->data);
}


term_t mk_bvsmod(term_manager_t *manager, term_t t1, term_t t2) {
  term_table_t *tbl;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
         && term_type(tbl, t1) == term_type(tbl, t2));

  switch (term_kind(tbl, t2)) {
  case BV64_CONSTANT:
    if (term_kind(tbl, t1) == BV64_CONSTANT) {
      return bvsmod_const64(manager, bvconst64_term_desc(tbl, t1), bvconst64_term_desc(tbl, t2));
    }
    break;

  case BV_CONSTANT:
    if (term_kind(tbl, t1) == BV_CONSTANT) {
      return bvsmod_const(manager, bvconst_term_desc(tbl, t1), bvconst_term_desc(tbl, t2));
    }
    break;

  default:
    break;
  }

  return bvsmod_term(tbl, t1, t2);
}




/*****************
 *  BIT EXTRACT  *
 ****************/

/*
 * Extract bit i of t
 * - t must be a bitvector term
 * - i must be between 0 and n-1, where n = bitsize of t
 *
 * The result is a boolean term
 */
term_t mk_bitextract(term_manager_t *manager, term_t t, uint32_t i) {
  term_table_t *tbl;
  bvconst64_term_t *d;
  bvconst_term_t *c;
  composite_term_t *bv;
  term_t u;

  tbl = manager->terms;

  assert(is_bitvector_term(tbl, t) && 0 <= i && i < term_bitsize(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    d = bvconst64_term_desc(tbl, t);
    u = bool2term(tst_bit64(d->value, i));
    break;

  case BV_CONSTANT:
    c = bvconst_term_desc(tbl, t);
    u = bool2term(bvconst_tst_bit(c->data, i));
    break;

  case BV_ARRAY:
    bv = bvarray_term_desc(tbl, t);
    u = bv->arg[i];
    break;

  default:
    u = bit_term(tbl, i, t);
    break;
  }

  return u;
}


/*
 * Convert bit i of buffer b to a term then reset b
 */
term_t bvl_get_bit(term_manager_t *manager, bvlogic_buffer_t *b, uint32_t i) {
  term_t t;

  assert(i < b->bitsize);
  t = map_bit_to_term(manager, b->bit[i]);
  bvlogic_buffer_clear(b);

  return t;
}






/**********************
 *  BIT-VECTOR ATOMS  *
 *********************/

/*
 * For debugging: check that t1 and t2 are bitvectors terms of the same size
 */
#ifndef NDEBUG

static bool valid_bvcomp(term_table_t *tbl, term_t t1, term_t t2) {
  return is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2)
    && term_type(tbl, t1) == term_type(tbl, t2);
}

#endif


/*
 * Unsigned comparison
 */

// check whether t1 < t2 holds trivially
static bool must_lt(term_manager_t *manager, term_t t1, term_t t2) {
  bvconstant_t *bv1, *bv2;

  bv1 = &manager->bv1;
  bv2 = &manager->bv2;
  upper_bound_unsigned(manager->terms, t1, bv1); // t1 <= bv1
  lower_bound_unsigned(manager->terms, t2, bv2); // bv2 <= t2
  assert(bv1->bitsize == bv2->bitsize);

  return bvconst_lt(bv1->data, bv2->data, bv1->bitsize);
}

// check whether t1 <= t2 holds trivially
static bool must_le(term_manager_t *manager, term_t t1, term_t t2) {
  bvconstant_t *bv1, *bv2;

  bv1 = &manager->bv1;
  bv2 = &manager->bv2;
  upper_bound_unsigned(manager->terms, t1, bv1);
  lower_bound_unsigned(manager->terms, t2, bv2);
  assert(bv1->bitsize == bv2->bitsize);

  return bvconst_le(bv1->data, bv2->data, bv1->bitsize);
}

 // t1 >= t2: unsigned
term_t mk_bvge(term_manager_t *manager, term_t t1, term_t t2) {
  assert(valid_bvcomp(manager->terms, t1, t2));

  if (t1 == t2 || must_le(manager, t2, t1)) {
    return true_term;
  }

  if (must_lt(manager, t1, t2)) {
    return false_term;
  }

  if (bvterm_is_min_unsigned(manager->terms, t1)) {
    // 0b0000..00 >= t2  iff t2 == 0b0000..00
    return mk_bitvector_eq(manager, t1, t2);
  }

  if (bvterm_is_max_unsigned(manager->terms, t2)) {
    // t1 >= 0b1111..11  iff t1 == 0b1111..11
    return mk_bitvector_eq(manager, t1, t2);
  }

  return bvge_atom(manager->terms, t1, t2);
}

// t1 > t2: unsigned
term_t mk_bvgt(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_bvge(manager, t2, t1));
}

// t1 <= t2: unsigned
term_t mk_bvle(term_manager_t *manager, term_t t1, term_t t2) {
  return mk_bvge(manager, t2, t1);
}

// t1 < t2: unsigned
term_t mk_bvlt(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_bvge(manager, t1, t2));
}




/*
 * Signed comparisons
 */

// Check whether t1 < t2 holds trivially
static bool must_slt(term_manager_t *manager, term_t t1, term_t t2) {
  bvconstant_t *bv1, *bv2;

  bv1 = &manager->bv1;
  bv2 = &manager->bv2;
  upper_bound_signed(manager->terms, t1, bv1);
  lower_bound_signed(manager->terms, t2, bv2);
  assert(bv1->bitsize == bv2->bitsize);

  return bvconst_slt(bv1->data, bv2->data, bv1->bitsize);
}

// Check whether t1 <= t2 holds
static bool must_sle(term_manager_t *manager, term_t t1, term_t t2) {
  bvconstant_t *bv1, *bv2;

  bv1 = &manager->bv1;
  bv2 = &manager->bv2;
  upper_bound_signed(manager->terms, t1, bv1);
  lower_bound_signed(manager->terms, t2, bv2);
  assert(bv1->bitsize == bv2->bitsize);

  return bvconst_sle(bv1->data, bv2->data, bv1->bitsize);
}

// t1 >= t2: signed
term_t mk_bvsge(term_manager_t *manager, term_t t1, term_t t2) {
  assert(valid_bvcomp(manager->terms, t1, t2));

  if (t1 == t2 || must_sle(manager, t2, t1)) {
    return true_term;
  }

  if (must_slt(manager, t1, t2)) {
    return false_term;
  }

  if (bvterm_is_min_signed(manager->terms, t1)) {
    // 0b1000..00 >= t2  iff t2 == 0b1000..00
    return mk_bitvector_eq(manager, t1, t2);
  }

  if (bvterm_is_max_signed(manager->terms, t2)) {
    // t1 >= 0b0111..11  iff t1 == 0b0111..11
    return mk_bitvector_eq(manager, t1, t2);
  }

  return bvsge_atom(manager->terms, t1, t2);
}

// t1 > t2: signed
term_t mk_bvsgt(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_bvsge(manager, t2, t1));
}


// t1 <= t2: signed
term_t mk_bvsle(term_manager_t *manager, term_t t1, term_t t2) {
  return mk_bvsge(manager, t2, t1);
}

// t1 < t2: signed
term_t mk_bvslt(term_manager_t *manager, term_t t1, term_t t2) {
  return opposite_term(mk_bvsge(manager, t1, t2));
}




/*************************************
 *  POWER-PRODUCTS AND POLYNOMIALS   *
 ************************************/

/*
 * Arithmetic product:
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n arithmetic terms
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 */
term_t mk_arith_pprod(term_manager_t *mngr, pprod_t *p, uint32_t n, const term_t *a) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(n == p->len);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_arith_buffer(mngr);

  rba_buffer_set_one(b); // b := 1
  for (i=0; i<n; i++) {
    // b := b * a[i]^e[i]
    rba_buffer_mul_term_power(b, tbl, a[i], p->prod[i].exp);
  }

  return mk_arith_term(mngr, b);
}


/*
 * Bitvector product: 1 to 64 bits vector
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n bitvector terms
 * - nbits = number of bits in each term of a
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 */
term_t mk_bvarith64_pprod(term_manager_t *mngr, pprod_t *p, uint32_t n, const term_t *a, uint32_t nbits) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(n == p->len && 0 < nbits && nbits <= 64);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith64_buffer(mngr);

  bvarith64_buffer_prepare(b, nbits);
  bvarith64_buffer_set_one(b); // b := 1
  for (i=0; i<n; i++) {
    // b := b * a[i]^e[i]
    bvarith64_buffer_mul_term_power(b, tbl, a[i], p->prod[i].exp);
  }

  return mk_bvarith64_term(mngr, b);
}


/*
 * Bitvector product: more than 64 bits
 * - p is a power product descriptor: t_0^e_0 ... t_{n-1}^e_{n-1}
 * - a is an array of n bitvector terms
 * - nbits = number of bits in each term of a
 * - this function constructs the term a[0]^e_0 ... a[n-1]^e_{n-1}
 */
term_t mk_bvarith_pprod(term_manager_t *mngr, pprod_t *p, uint32_t n, const term_t *a, uint32_t nbits) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(n == p->len && 64 < nbits && nbits <= YICES_MAX_BVSIZE);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith_buffer(mngr);

  bvarith_buffer_prepare(b, nbits);
  bvarith_buffer_set_one(b); // b := 1
  for (i=0; i<n; i++) {
    // b := b * a[i]^e[i]
    bvarith_buffer_mul_term_power(b, tbl, a[i], p->prod[i].exp);
  }

  return mk_bvarith_term(mngr, b);
}


/*
 * Generic version: check the type of a[0]
 */
term_t mk_pprod(term_manager_t *mngr, pprod_t *p, uint32_t n, const term_t *a) {
  type_t tau;
  uint32_t nbits;

  assert(n > 0);

  tau = term_type(mngr->terms, a[0]);
  if (is_arithmetic_type(tau)) {
    return mk_arith_pprod(mngr, p, n, a);
  } else {
    nbits = bv_type_size(mngr->types, tau);
    if (nbits <= 64) {
      return mk_bvarith64_pprod(mngr, p, n, a, nbits);
    } else {
      return mk_bvarith_pprod(mngr, p, n, a, nbits);
    }
  }
}

/*
 * Polynomial:
 * - p is a polynomial c_0 t_0 + c_1 t_1 + ... + c_{n-1} t_{n-1}
 * - a is an array of n terms
 * - construct the term c_0 a[0] + c_1 a[1] + ... + c_{n-1} a[n-1]
 *   except that c_i * a[i] is replaced by c_i if a[i] == const_idx.
 */
term_t mk_arith_poly(term_manager_t *mngr, polynomial_t *p, uint32_t n, const term_t *a) {
  rba_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(p->nterms == n);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_arith_buffer(mngr);
  reset_rba_buffer(b);

  for (i=0; i<n; i++) {
    if (a[i] == const_idx) {
      rba_buffer_add_const(b, &p->mono[i].coeff);
    } else {
      rba_buffer_add_const_times_term(b, tbl, &p->mono[i].coeff, a[i]);
    }
  }

  return mk_arith_term(mngr, b);
}


/*
 * Same thing for a bitvector polynomial (1 to 64bits)
 */
term_t mk_bvarith64_poly(term_manager_t *mngr, bvpoly64_t *p, uint32_t n, const term_t *a) {
  bvarith64_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(p->nterms == n && 0 < p->bitsize && p->bitsize <= 64);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith64_buffer(mngr);
  bvarith64_buffer_prepare(b, p->bitsize);

  for (i=0; i<n; i++) {
    if (a[i] == const_idx) {
      bvarith64_buffer_add_const(b, p->mono[i].coeff);
    } else {
      bvarith64_buffer_add_const_times_term(b, tbl, p->mono[i].coeff, a[i]);
    }
  }

  return mk_bvarith64_term(mngr, b);
}


/*
 * Same thing for a bitvector polynomial (more than 64bits)
 */
term_t mk_bvarith_poly(term_manager_t *mngr, bvpoly_t *p, uint32_t n, const term_t *a) {
  bvarith_buffer_t *b;
  term_table_t *tbl;
  uint32_t i;

  assert(p->nterms == n && 64 < p->bitsize && p->bitsize <= YICES_MAX_BVSIZE);

  tbl = term_manager_get_terms(mngr);
  b = term_manager_get_bvarith_buffer(mngr);
  bvarith_buffer_prepare(b, p->bitsize);

  for (i=0; i<n; i++) {
    if (a[i] == const_idx) {
      bvarith_buffer_add_const(b, p->mono[i].coeff);
    } else {
      bvarith_buffer_add_const_times_term(b, tbl, p->mono[i].coeff, a[i]);
    }
  }

  return mk_bvarith_term(mngr, b);
}



/*
 * Support for elimating arithmetic variables:
 * - given a polynomial p and a term t that occurs in p
 * - construct the polynomial q such that (t == q) is equivalent to (p == 0)
 *   (i.e., write p as a.t + r and construct  q :=  -r/a).
 */
term_t mk_arith_elim_poly(term_manager_t *mngr, polynomial_t *p, term_t t) {
  rba_buffer_t *b;
  rational_t *a;
  uint32_t i, j, n;

  assert(good_term(mngr->terms, t));

  n = p->nterms;

  // find j such that p->mono[j].var == t
  j = 0;
  while (p->mono[j].var != t) {
    j++;
    assert(j < n);
  }

  a = &p->mono[j].coeff; // coefficient of t in p
  assert(q_is_nonzero(a));

  /*
   * p is r + a.t, construct -r/a in buffer b
   */
  b = term_manager_get_arith_buffer(mngr);
  reset_rba_buffer(b);
  if (q_is_minus_one(a)) {
    // special case: a = -1
    i = 0;
    if (p->mono[0].var == const_idx) {
      assert(j > 0);
      rba_buffer_add_const(b, &p->mono[0].coeff);
      i ++;
    }
    while (i < n) {
      if (i != j) {
	assert(p->mono[i].var != t);
	rba_buffer_add_varmono(b, &p->mono[i].coeff, p->mono[i].var);
      }
      i++;
    }
  } else {
    // first construct -r then divide by a
    i = 0;
    if (p->mono[0].var == const_idx) {
      assert(j > 0);
      rba_buffer_sub_const(b, &p->mono[0].coeff);
      i ++;
    }
    while (i < n) {
      if (i != j) {
	assert(p->mono[i].var != t);
	rba_buffer_sub_varmono(b, &p->mono[i].coeff, p->mono[i].var);
      }
      i ++;
    }
    if (! q_is_one(a)) {
      rba_buffer_div_const(b, a);
    }
  }

  return mk_arith_term(mngr, b);
}

