/*
 * TERM MANAGER
 */

#include <stdint.h>
#include <assert.h>

#include "int_array_sort.h"
#include "int_vectors.h"
#include "memalloc.h"
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
 * - n = initial term table size
 * - types = attached type table
 */
void init_term_manager(term_manager_t *manager, type_table_t *types, uint32_t n) {
  init_pprod_table(&manager->pprods, 0);
  init_term_table(&manager->terms, n, types, &manager->pprods);
  manager->types = types;

  manager->arith_buffer = NULL;
  manager->bvarith_buffer = NULL;
  manager->bvarith64_buffer = NULL;
  manager->bvlogic_buffer = NULL;

  manager->arith_store = NULL;
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

object_store_t *term_manager_get_arith_store(term_manager_t *manager) {
  object_store_t *tmp;

  tmp = manager->arith_store;
  if (tmp == NULL) {
    tmp = (object_store_t *) safe_malloc(sizeof(object_store_t));
    init_mlist_store(tmp);
    manager->arith_store = tmp;
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
arith_buffer_t *term_manager_get_arith_buffer(term_manager_t *manager) {
  arith_buffer_t *tmp;
  object_store_t *mstore;

  tmp = manager->arith_buffer;
  if (tmp == NULL) {
    mstore = term_manager_get_arith_store(manager);
    tmp = (arith_buffer_t *) safe_malloc(sizeof(arith_buffer_t));
    init_arith_buffer(tmp, &manager->pprods, mstore);
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
    init_bvarith_buffer(tmp, &manager->pprods, mstore);
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
    init_bvarith64_buffer(tmp, &manager->pprods, mstore);
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

static void term_manager_free_arith_store(term_manager_t *manager) {
  object_store_t *tmp;

  tmp = manager->arith_store;
  if (tmp != NULL) {
    delete_mlist_store(tmp);
    safe_free(tmp);
    manager->arith_store = NULL;
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
  arith_buffer_t *tmp;

  tmp = manager->arith_buffer;
  if (tmp != NULL) {
    delete_arith_buffer(tmp);
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


extern void delete_term_manager(term_manager_t *manager) {
  term_manager_free_arith_buffer(manager);
  term_manager_free_bvarith_buffer(manager);
  term_manager_free_bvarith64_buffer(manager);
  term_manager_free_bvlogic_buffer(manager);

  term_manager_free_arith_store(manager);
  term_manager_free_bvarith_store(manager);
  term_manager_free_bvarith64_store(manager);
  term_manager_free_nodes(manager);

  q_clear(&manager->r0);
  delete_bvconstant(&manager->bv0);
  delete_bvconstant(&manager->bv1);
  delete_bvconstant(&manager->bv2);
  delete_ivector(&manager->vector0);

  delete_term_table(&manager->terms);
  delete_pprod_table(&manager->pprods);
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

  terms = &manager->terms;

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
 * Check whether x is (bveq a 0b0) or (bveq a 0b1) where a is a term 
 * of type (bitvector 1).
 * - if x is (bveq a 0b0): return a and set polarity to false
 * - if x is (bveq a 0b1): return a and set polarity to true
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
	*polarity = (bool) c->value;
	return b;
      }

      if (term_kind(tbl, b) == BV64_CONSTANT) {
	// b is either 0b0 or 0b1
	c = bvconst64_term_desc(tbl, b);
	assert(c->value == 0 || c->value == 1);
	*polarity = (bool) c->value;
	return a;
      }
    }
  }

  return NULL_TERM;
}


/*
 * Auxiliary function: build (bveq t1 t2)
 * - try to simplify to true or false
 * - attempt to simplify the equality if it's between bit-arrays or bit-arrays and constant
 * - build an atom if no simplification works
 */
static term_t mk_bitvector_eq(term_table_t *tbl, term_t t1, term_t t2) {
  term_t aux;

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
   * Default: normalize then build a bveq_atom
   */
  if (t1 > t2) {
    aux = t1; t1 = t2; t2 = aux;
  }

  return bveq_atom(tbl, t1, t2);
}



/*
 * Special constructor for (iff x y) when x or y (or both)
 * is of the form (bveq a 0b0) or (bveq a 0b1).
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

  tbl = &manager->terms;

  a = term_is_bveq1(tbl, x, &pa);
  b = term_is_bveq1(tbl, y, &pb);
  if (a != NULL_TERM || b != NULL_TERM) {
    if (a != NULL_TERM && b != NULL_TERM) {
      /*
       * x is (bveq a <constant>)
       * y is (bveq b <constant>)
       */
      t = mk_bitvector_eq(tbl, a, b);
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
      t = mk_bitvector_eq(tbl, a, t);
      t = signed_term(t, pa);
      return t;
    }

    if (b != NULL_TERM) {
      /*
       * y is (bveq b <constant>)
       */
      t = bvarray_get_term(manager, &x, 1);
      t = mk_bitvector_eq(tbl, b, t);
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

  return or_term(&manager->terms, 2, aux);
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
  return kind_for_idx(&manager->terms, index_of(x)) == UNINTERPRETED_TERM;
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

  return eq_term(&manager->terms, x, y);
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
    return or_term(&manager->terms, j, a);
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
    return eq_term(&manager->terms, x, y);
  }

  // general case: j >= 3
  x = xor_term(&manager->terms, j, a);
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

  tbl = &manager->terms;

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

  assert(term_type(&manager->terms, x) == term_type(&manager->terms, y) && 
	 term_type(&manager->terms, x) == term_type(&manager->terms, z));

  ite = mk_bv_ite(manager, c, y, z);

  // normalize (bveq x ite): put smaller index on the left
  if (x > ite) {
    aux = x; x = ite; ite = aux;
  }

  return bveq_atom(&manager->terms, x, ite);
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

  tbl = &manager->terms;

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

  if (term_kind(&manager->terms, x) == BV_EQ_ATOM && 
      term_kind(&manager->terms, y) == BV_EQ_ATOM) {
    return mk_lifted_ite_bveq(manager, c, x, y);
  }

  return ite_term(&manager->terms, bool_type(manager->types), c, x, y);
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
 * Convert b to a term and reset b:
 * - if b is a constant: return an arith constant term
 * - if b is of the form 1 . t: return t
 * - if b is of the form 1 . x_1^d_1 ... x_n^d_n: build a power product
 * - othwerwise: build a polynomial term
 */
static term_t arith_buffer_to_term(term_table_t *tbl, arith_buffer_t *b) {
  mlist_t *m;
  pprod_t *r;
  uint32_t n;
  term_t t;

  assert(b->ptbl == tbl->pprods);

  n = b->nterms;
  if (n == 0) {
    t = zero_term;
  } else if (n == 1) {
    m = b->list; // unique monomial of b
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

  arith_buffer_reset(b);

  return t;
}


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
  arith_buffer_t *b;
  monomial_t *mono;
  uint32_t i;
  term_t x;

  assert(q_is_nonzero(c));

  b = term_manager_get_arith_buffer(manager);
  arith_buffer_reset(b);

  i = 0;
  mono = p->mono;
  x = mono->var;

  // deal with the constant if any
  if (x == const_idx) {
    if (x == a[i]) {
      i ++;
    } else {
      assert(x < a[i]);
      arith_buffer_add_const(b, &mono->coeff);
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
      arith_buffer_add_mono(b, &mono->coeff, pprod_for_term(&manager->terms, x));
    }
    mono ++;
    x = mono->var;
  }

  // divide by c
  if (! q_is_one(c)) {
    arith_buffer_div_const(b, c);
  }

  // build the term from b
  arith_buffer_normalize(b);
  return arith_buffer_to_term(&manager->terms, b);
}  


/*
 * Remove every monomial of p whose variable is not in a
 * then add c * t to the result.
 * - a must be an array of terms sorted in increasing order and terminated by max_idx
 * - all elements of a must be variables of p
 */
static term_t add_mono_to_common_part(term_manager_t *manager, polynomial_t *p, term_t *a, rational_t *c, term_t t) {
  term_table_t *tbl;
  arith_buffer_t *b;
  monomial_t *mono;
  uint32_t i;
  term_t x;

  tbl = &manager->terms;
  b = term_manager_get_arith_buffer(manager);
  arith_buffer_reset(b);  

  i = 0;
  mono = p->mono;
  x = mono->var;

  // constant monomial
  if (x == const_idx) {
    assert(x <= a[i]);
    if (x == a[i]) {
      arith_buffer_add_const(b, &mono->coeff);
      i ++;
    }
    mono ++;
    x = mono->var;
  }

  // non constant monomials
  while (x < max_idx) {
    assert(x <= a[i]);
    if (x == a[i]) {
      arith_buffer_add_mono(b, &mono->coeff, pprod_for_term(tbl, x));
      i ++;
    }
    mono ++;
    x = mono->var;
  }

  // add c * t
  arith_buffer_add_mono(b, c, pprod_for_term(tbl, t));

  arith_buffer_normalize(b);
  return arith_buffer_to_term(tbl, b);
}



/*
 * Build  t := p/c where c is a non-zero rational
 * - b = buffer for computation
 */
static term_t polynomial_div_const(term_manager_t *manager, polynomial_t *p, rational_t *c) {
  term_table_t *tbl;
  arith_buffer_t *b;

  tbl = &manager->terms;
  b = term_manager_get_arith_buffer(manager);
  arith_buffer_reset(b);

  arith_buffer_add_monarray(b, p->mono, pprods_for_poly(tbl, p));
  term_table_reset_pbuffer(tbl);
  arith_buffer_div_const(b, c);

  return arith_buffer_to_term(tbl, b);
}


/*
 * Build t := u * c
 * - b = buffer for computation
 */
static term_t mk_mul_term_const(term_manager_t *manager, term_t t, rational_t *c) {
  term_table_t *tbl;
  arith_buffer_t *b;

  tbl = &manager->terms;
  b = term_manager_get_arith_buffer(manager);
  arith_buffer_reset(b);
  arith_buffer_add_mono(b, c, pprod_for_term(tbl, t));

  return arith_buffer_to_term(tbl, b);
}


/*
 * Attempt to rewrite (ite c t e) to (r + a * (ite c t' e'))
 * - t and e must be distinct integer polynomials
 * - if r is null and a is one, it builds (ite c t e)
 * - if r is null and a is more than one, it builds a * (ite t' e')
 * - b = buffer to be used for computation
 */
static term_t mk_integer_polynomial_ite(term_manager_t *manager, term_t c, term_t t, term_t e) {
  term_table_t *tbl;
  polynomial_t *p, *q;
  ivector_t *v;
  rational_t *r0;
  term_t ite;

  tbl = &manager->terms;

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
    assert(is_boolean_term(&manager->terms, t) && 
	   is_boolean_term(&manager->terms, e));
    return mk_bool_ite(manager, c, t, e);
  }

  // bit-vector ite
  if (is_bv_type(manager->types, tau)) {
    assert(is_bitvector_term(&manager->terms, t) &&
	   is_bitvector_term(&manager->terms, e));
    return mk_bv_ite(manager, c, t, e);
  }

  // general case
  if (c == true_term) return t;
  if (c == false_term) return e;

  t = simplify_in_context(&manager->terms, c, t);
  e = simplify_in_context(&manager->terms, opposite_term(c), e);
  if (t == e) return t;

  if (is_neg_term(c)) {
    // ite (not c) x y  --> ite c y x
    c = opposite_term(c);
    aux = t; t = e; e = aux;
  }

#if 1
  // check whether both sides are integer polynomials
  if (is_integer_type(tau) 
      && term_kind(&manager->terms, t) == ARITH_POLY 
      && term_kind(&manager->terms, e) == ARITH_POLY) {
    return mk_integer_polynomial_ite(manager, c, t, e);
  }
#endif

  return ite_term(&manager->terms, tau, c, t, e);
}







#if 0

/***********************************************
 *  CONVERSION OF ARITHMETIC BUFFERS TO TERMS  *
 **********************************************/


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
 * - try simplication and normalize first
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




/********************************************
 *  CONVERSION OF BVLOGIC BUFFERS TO TERMS  *
 *******************************************/

/*
 * Convert buffer b to a bv_constant term
 * - side effect: use bv0
 */
static term_t bvlogic_buffer_get_bvconst(term_manager_t *manager, bvlogic_buffer_t *b) {
  bvconstant_t *bv;

  assert(bvlogic_buffer_is_constant(b));

  bv = &manager->bv0;
  bvlogic_buffer_get_constant(b, bv);
  return bvconst_term(&manager->terms, bv->bitsize, bv->data);
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

  terms = &manager->terms;

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
term_t bvlogic_buffer_get_term(bvlogic_buffer_t *b) {
  term_t t;
  uint32_t n;

  n = b->bitsize;
  assert(n > 0);
  if (bvlogic_buffer_is_constant(b)) {
    if (n <= 64) {
      // small constant
      t = bv64_constant(&terms, n, bvlogic_buffer_get_constant64(b));
    } else {
      // wide constant
      t = bvlogic_buffer_get_bvconst(b);
    }

  } else {
    t = bvlogic_buffer_get_var(b);
    if (t < 0 || term_bitsize(&terms, t) != n) {
      // not a variable
      t = bvlogic_buffer_get_bvarray(b);
    }
  }

  assert(is_bitvector_term(&terms, t) && term_bitsize(&terms, t) == n);

  bvlogic_buffer_clear(b);
  
  return t;
}



/********************************************
 *  CONVERSION OF BVARITH BUFFERS TO TERMS  *
 *******************************************/

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
static composite_term_t *pprod_get_bvarray(pprod_t *r) {  
  composite_term_t *bv;
  term_t t;

  bv = NULL;
  if (pp_is_var(r)) {
    t = var_of_pp(r);
    if (term_kind(&terms, t) == BV_ARRAY) {
      bv = composite_for_idx(&terms, index_of(t));
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
static term_t convert_bvarith_to_bvarray(bvarith_buffer_t *b) {
  composite_term_t *bv;
  bvmlist_t *m;
  uint32_t n;

  n = b->bitsize;
  m = b->list; // first monomial
  if (m->prod == empty_pp) {
    // copy constant into vector0
    bvarray_copy_constant(&vector0, n, m->coeff);
    m = m->next;
  } else {
    // initialze vector0 to 0
    bvarray_set_zero_bv(&vector0, n);
  }

  while (m->next != NULL) {
    bv = pprod_get_bvarray(m->prod);
    if (bv == NULL) return NULL_TERM;

    assert(bv->arity == n);

    // try to convert coeff * v into shift + bitwise or 
    if (! bvarray_check_addmul(&vector0, n, m->coeff, bv->arg)) {
      return NULL_TERM;  // conversion failed
    }
    m = m->next;
  }

  // Success: construct a bit array from log_buffer
  return bvarray_term(&terms, n, vector0.data);
}


/*
 * Attempt to convert a bvarith64 buffer to a bv-array term
 * - b = bvarith buffer (list of monomials)
 * - return NULL_TERM if the conversion fails
 * - return a term t if the conversion succeeds.
 * - side effect: use vector0
 */
static term_t convert_bvarith64_to_bvarray(bvarith64_buffer_t *b) {
  composite_term_t *bv;
  bvmlist64_t *m;
  uint32_t n;

  n = b->bitsize;
  m = b->list; // first monomial
  if (m->prod == empty_pp) {
    // copy constant into vector0
    bvarray_copy_constant64(&vector0, n, m->coeff);
    m = m->next;
  } else {
    // initialze vector0 to 0
    bvarray_set_zero_bv(&vector0, n);
  }

  while (m->next != NULL) {
    bv = pprod_get_bvarray(m->prod);
    if (bv == NULL) return NULL_TERM;

    assert(bv->arity == n);

    // try to convert coeff * v into shift + bitwise or 
    if (! bvarray_check_addmul64(&vector0, n, m->coeff, bv->arg)) {
      return NULL_TERM;  // conversion failed
    }
    m = m->next;
  }

  // Success: construct a bit array from log_buffer
  return bvarray_term(&terms, n, vector0.data);
}


/*
 * Constant bitvector with all bits 0
 * - n = bitsize (must satisfy 0 < n && n <= YICES_MAX_BVSIZE)
 * - side effect: modify bv0
 */
static term_t make_zero_bv(uint32_t n) {
  assert(0 < n && n <= YICES_MAX_BVSIZE);
  if (n > 64) {
    bvconstant_set_all_zero(&bv0, n);
    return bvconst_term(&terms, bv0.bitsize, bv0.data);
  } else {
    return bv64_constant(&terms, n, 0);
  }
}


/*
 * These functions are not part of the API.
 * They are exported to be used by other yices modules.
 */

/*
 * Normalize b then convert it to a term and reset b
 *
 * if b is reduced to a single variable x, return the term attached to x
 * if b is reduced to a power product, return that
 * if b is constant, build a BV_CONSTANT term
 * if b can be converted to a BV_ARRAY term do it
 * otherwise construct a BV_POLY
 */
term_t bvarith_buffer_get_term(bvarith_buffer_t *b) {
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
    t = make_zero_bv(n);
    goto done;
  }

  if (p == 1) {
    m = b->list; // unique monomial of b
    r = m->prod;
    if (r == empty_pp) {
      // constant 
      t = bvconst_term(&terms, n, m->coeff);
      goto done;
    }
    if (bvconst_is_one(m->coeff, k)) {
      // power product
      t = pp_is_var(r) ? var_of_pp(r) : pprod_term(&terms, r);
      goto done;
    } 
  }

  // try to convert to a bvarray term
  t = convert_bvarith_to_bvarray(b);
  if (t == NULL_TERM) {
    // conversion failed: build a bvpoly
    t = bv_poly(&terms, b);
  }

 done:
  bvarith_buffer_prepare(b, 32); // reset b, any positive n would do
  assert(is_bitvector_term(&terms, t) && term_bitsize(&terms, t) == n);

  return t;  
}



/*
 * Normalize b then convert it to a term and reset b
 *
 * if b is reduced to a single variable x, return the term attached to x
 * if b is reduced to a power product, return that
 * if b is constant, build a BV64_CONSTANT term
 * if b can be converted to a BV_ARRAY term do it
 * otherwise construct a BV64_POLY
 */
term_t bvarith64_buffer_get_term(bvarith64_buffer_t *b) {
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
    t = make_zero_bv(n);
    goto done;
  }

  if (p == 1) {
    m = b->list; // unique monomial of b
    r = m->prod;
    if (r == empty_pp) {
      // constant 
      t = bv64_constant(&terms, n, m->coeff);
      goto done;
    }
    if (m->coeff == 1) {
      // power product
      t = pp_is_var(r) ? var_of_pp(r) : pprod_term(&terms, r);
      goto done;
    }
  }

  // try to convert to a bvarray term
  t = convert_bvarith64_to_bvarray(b);
  if (t == NULL_TERM) {
    // conversion failed: build a bvpoly
    t = bv64_poly(&terms, b);
  }

 done:
  bvarith64_buffer_prepare(b, 32); // reset b, any positive n would do
  assert(is_bitvector_term(&terms, t) && term_bitsize(&terms, t) == n);

  return t;  
}






/*
 * LIFT IF
 */

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
 */
typedef struct lift_result_s {
  term_t cond;
  term_t left1, left2;
  term_t right1, right2;
} lift_result_t;


static bool check_for_lift_if(term_table_t *tbl, term_t t1, term_t t2, lift_result_t *d) {
  composite_term_t *ite1, *ite2;
  term_t cond;

  if (is_ite_term(tbl, t1)) {
    if (is_ite_term(tbl, t2)) {
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
  } else if (is_ite_term(tbl, t2)) {
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



#endif
