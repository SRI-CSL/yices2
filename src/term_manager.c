/*
 * TERM MANAGER
 */

#include <stdint.h>
#include <assert.h>

#include "int_array_sort.h"
#include "int_vectors.h"
#include "memalloc.h"
#include "bit_tricks.h"
#include "bv64_constants.h"
#include "bv_constants.h"
#include "bit_term_conversion.h"
#include "term_utils.h"

#include "term_manager.h"



/************************
 *  GENERAL OPERATIONS  *
 ***********************/

/*
 * Initialization:
 * - terms = attached term table
 * - types = attached type table
 */
void init_term_manager(term_manager_t *manager, type_table_t *types, term_table_t *terms) {
  manager->terms = terms;
  manager->types = types;
  manager->pprods = terms->pprods;

  manager->bvarith_buffer = NULL;
  manager->bvarith64_buffer = NULL;
  manager->bvlogic_buffer = NULL;

  manager->bvarith_store = NULL;
  manager->bvarith64_store = NULL;
  manager->nodes = NULL;

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


extern void delete_term_manager(term_manager_t *manager) {
  term_manager_free_bvarith_buffer(manager);
  term_manager_free_bvarith64_buffer(manager);
  term_manager_free_bvlogic_buffer(manager);

  term_manager_free_bvarith_store(manager);
  term_manager_free_bvarith64_store(manager);
  term_manager_free_nodes(manager);

  delete_bvconstant(&manager->bv0);
  delete_bvconstant(&manager->bv1);
  delete_bvconstant(&manager->bv2);
  delete_ivector(&manager->vector0);
}






/************************************************
 *  CONVERSION OF ARRAYS OF BOOLEANS TO TERMS   *
 ***********************************************/

/*
 * Check whether all elements of a are boolean constants
 * - n = size of the array
 */
static bool bvarray_is_constant(term_t *a, uint32_t n) {
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
static uint64_t bvarray_get_constant64(term_t *a, uint32_t n) {
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
static void bvarray_get_constant(term_t *a, uint32_t n, bvconstant_t *c) {
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
 * Check whether b is of the form (bit 0 x) ... (bit n-1 x)
 * - if so return x
 * - otherwise return NULL_TERM
 */
static term_t bvarray_get_var(term_table_t *tbl, term_t *a, uint32_t n) {
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
static term_t bvarray_get_term(term_manager_t *manager, term_t *a, uint32_t n) {
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
 * Rewrite (xor x y) to (iff (not x) y)
 */
term_t mk_binary_xor(term_manager_t *manager, term_t x, term_t y) {
  return mk_iff(manager, opposite_term(x), y);
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

  return ite_term(manager->terms, tau, c, t, e);
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
  assert(i >= 0);
  return constant_term(manager->terms, tau, i);
}


/*
 * New uninterpreted term of type tau
 * - i.e., this creates a fresh global variable
 */
term_t mk_uterm(term_manager_t *manager, type_t tau) {
  return new_uninterpreted_term(manager->terms, tau);
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
  term_table_t *terms;
  node_table_t *nodes;
  uint32_t i, n;

  nodes = manager->nodes;
  assert(b->nodes == nodes && nodes != NULL);

  terms = manager->terms;

  // translate each bit of b into a boolean term
  // we store the translation in b->bit
  n = b->bitsize;
  for (i=0; i<n; i++) {
    b->bit[i] = convert_bit_to_term(terms, nodes, b->bit[i]);
  }

  // build the term (bvarray b->bit[0] ... b->bit[n-1])
  return bvarray_term(terms, n, b->bit);
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
term_t mk_bvarray(term_manager_t *manager, uint32_t n, term_t *a) {
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
    k = ctz64(b->value); // ctz64 not defined in value = 0
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




