/*
 * UTILITIES FOR SIMPLIFYING TERMS
 */


#include <assert.h>

#include "bv64_constants.h"
#include "term_utils.h"



/***********************************
 *  OPERATIONS ON BIT ARRAY TERMS  *
 **********************************/

/*
 * Upper/lower bound on a bitarray interpreted as an unsigned integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-1) a[n-1], with 0 <= a[i] <= 1
 * upper bound: replace a[i] by 1 if a[i] != 0
 * lower bound: replace a[i] by 0 if a[i] != 1
 */
static void bitarray_upper_bound_unsigned(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_one(c, n); // c := 0b1...1 (n bits)
  for (i=0; i<n; i++) {
    if (a->arg[i] == false_term) {
      bvconst_clr_bit(c->data, i);
    }
  }
}

static void bitarray_lower_bound_unsigned(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_zero(c, n); // c := 0b0...0 (n bits)
  for (i=0; i<n; i++) {
    if (a->arg[i] == true_term) {
      bvconst_set_bit(c->data, i);
    }
  }
}


/*
 * Upper/lower bound on a bitarray interpreted as a signed integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-2) a[n-2] - 2^(n-1) a[n-1]
 * upper bound: 
 *   for i=0 to n-2, replace a[i] by 1 if a[i] != 0 
 *   replace the sign bit a[n-1] by 0 unless a[n-1] = 1.
 * lower bound: 
 *   for i=0 to n-2, replace a[i] by 0 if a[i] != 1
 *   replace the sign bit a[n-1] by 1 unless a[n-1] = 0.
 */
static void bitarray_upper_bound_signed(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_one(c, n);

  for (i=0; i<n-1; i++) {
    if (a->arg[i] == false_term) {
      bvconst_clr_bit(c->data, i);
    }
  }

  if (a->arg[i] != true_term) {
    bvconst_clr_bit(c->data, i);
  }
}


static void bitarray_lower_bound_signed(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_zero(c, n);

  for (i=0; i<n-1; i++) {
    if (a->arg[i] == true_term) {
      bvconst_set_bit(c->data, i);
    }
  }

  if (a->arg[i] != false_term) {
    bvconst_set_bit(c->data, i);
  }
}




/*
 * BOUNDS FOR ARRAYS OF 1 TO 64BITS
 */

/*
 * Upper/lower bound on a bitarray interpreted as an unsigned integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-1) a[n-1], with 0 <= a[i] <= 1
 * upper bound: replace a[i] by 1 if a[i] != 0
 * lower bound: replace a[i] by 0 if a[i] != 1
 */
static uint64_t bitarray_upper_bound_unsigned64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = mask64(n); // c = 0001...1 (n lower bits set)
  for (i=0; i<n; i++) {
    if (a->arg[i] == false_term) {
      c = clr_bit64(c, i);
    }
  }

  assert(c == norm64(c, n));

  return c;
}

static uint64_t bitarray_lower_bound_unsigned64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n;

  assert(0 < a->arity && a->arity <= 64);
  
  n = a->arity;
  c = 0;
  for (i=0; i<n; i++) {
    if (a->arg[i] == true_term) {
      c = set_bit64(c, i);
    }
  }

  assert(c == norm64(c, n));

  return c;
}


/*
 * Upper/lower bound on a bitarray interpreted as a signed integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-2) a[n-2] - 2^(n-1) a[n-1]
 * upper bound: 
 *   for i=0 to n-2, replace a[i] by 1 if a[i] != 0 
 *   replace the sign bit a[n-1] by 0 unless a[n-1] = 1.
 * lower bound: 
 *   for i=0 to n-2, replace a[i] by 0 if a[i] != 1
 *   replace the sign bit a[n-1] by 1 unless a[n-1] = 0.
 */
static uint64_t bitarray_upper_bound_signed64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = mask64(n); // c = 0001...1
  for (i=0; i<n-1; i++) {
    if (a->arg[i] == false_term) {
      c = clr_bit64(c, i);
    }
  }

  if (a->arg[i] != true_term) {
    c = clr_bit64(c, i); // clear the sign bit
  }

  return c;
}


static uint64_t bitarray_lower_bound_signed64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = 0;

  for (i=0; i<n-1; i++) {
    if (a->arg[i] == true_term) {
      c = set_bit64(c, i);
    }
  }

  if (a->arg[i] != false_term) {
    c = set_bit64(c, i); // set the sign bit
  }

  return c;
}




/*
 * DISEQUALITY CHECKS
 */

/*
 * Disequality check between two bit arrays
 * - a and b must have the same arity
 * - all components must be boolean
 *
 * TODO?: improve this.
 * - we could try to see that (l l) can't be equal to (u (not u))
 */
static bool disequal_bitarrays(composite_term_t *a, composite_term_t *b) {
  uint32_t i, n;

  assert(a->arity == b->arity);

  n = a->arity;
  for (i=0; i<n; i++) {
    if (opposite_bool_terms(a->arg[i], b->arg[i])) return true;
  }

  return false;
}


/*
 * Disequality check between bit array a and small constant c
 * - both must have the same bit size
 */
static bool disequal_bitarray_bvconst64(composite_term_t *a, bvconst64_term_t *c) {
  uint32_t i, n;

  assert(a->arity == c->bitsize && 0 < a->arity && a->arity <= 64);

  n = a->arity;
  for (i=0; i<n; i++) {
    if (index_of(a->arg[i]) == bool_const) {
      assert(a->arg[i] == true_term || a->arg[i] == false_term);
      if (a->arg[i] != bool2term(tst_bit64(c->value, i))) {
	return true;
      }
    }
  }

  return false;
}


/*
 * Disequality check between bit array a and bv-constant c
 * - both must have the same bit size
 */
static bool disequal_bitarray_bvconst(composite_term_t *a, bvconst_term_t *c) {
  uint32_t i, n;

  assert(a->arity == c->bitsize && 64 < a->arity);

  n = a->arity;
  for (i=0; i<n; i++) {
    if (index_of(a->arg[i]) == bool_const) {
      assert(a->arg[i] == true_term || a->arg[i] == false_term);
      if (a->arg[i] != bool2term(bvconst_tst_bit(c->data, i))) {
	return true;
      }
    }
  }

  return false;
}





/******************************
 *  CHECKS FOR DISEQUALITIES  *
 *****************************/

/*
 * Base cases:
 * - x and y are both CONSTANT_TERM
 * - x and y are boolean and x = (not y).
 */
static inline bool disequal_constant_terms(term_t x, term_t y) {
  return x != y;
}

static inline bool disequal_boolean_terms(term_t x, term_t y) {
  return opposite_bool_terms(x, y);
}


/*
 * Arithmetic: x and y are both arithmetic terms
 *
 * The conversion of arith_buffer to terms ensures that polynomial
 * terms are not constant and not of the form 1.x for some term x.
 *
 * We can deal with 4 simple cases:
 * - both x and y are constant 
 * - both x and y are polynomials
 * - x is a polynomial and y is not a constant (i.e., y may occur as a variable in x)
 * - y is a polynomial and x is not a constant
 *
 * TODO? we could do more when (x - y) is a polynomial with integer variables.
 */
static bool disequal_arith_terms(term_table_t *tbl, term_t x, term_t y) {
  type_kind_t kx, ky;

  kx = term_kind(tbl, x);
  ky = term_kind(tbl, y);

  if (kx == ARITH_CONSTANT && ky == ARITH_CONSTANT) {  
    return x != y; // because of hash consing.
  } 
  
  if (kx == ARITH_POLY && ky == ARITH_POLY) {
    return disequal_polynomials(poly_term_desc(tbl, x), poly_term_desc(tbl, y));
  }
  
  if (kx == ARITH_POLY && ky != ARITH_CONSTANT) {
    return polynomial_is_const_plus_var(poly_term_desc(tbl, x), y);
  }

  if (ky == ARITH_POLY && kx != ARITH_CONSTANT) {
    return polynomial_is_const_plus_var(poly_term_desc(tbl, y), x);
  } 

  return false;
}





/*
 * Bitvectors: x and y are bitvector terms of 1 to 64 bits
 */
static bool disequal_bv64_terms(term_table_t *tbl, term_t x, term_t y) {
  term_kind_t kx, ky;

  kx = term_kind(tbl, x);
  ky = term_kind(tbl, y);

  if (kx == ky) {
    if (kx == BV64_CONSTANT) {
      return x != y;
    }

    if (kx == BV64_POLY) {
      return disequal_bvpoly64(bvpoly64_term_desc(tbl, x), bvpoly64_term_desc(tbl, y));
    }

    if (kx == BV_ARRAY) {
      return disequal_bitarrays(bvarray_term_desc(tbl, x), bvarray_term_desc(tbl, y));
    }

  } else {
   
    if (kx == BV64_CONSTANT && ky == BV_ARRAY) {
      return disequal_bitarray_bvconst64(bvarray_term_desc(tbl, y), bvconst64_term_desc(tbl, x));
    }

    if (ky == BV64_CONSTANT && kx == BV_ARRAY) {
      return disequal_bitarray_bvconst64(bvarray_term_desc(tbl, x), bvconst64_term_desc(tbl, y));
    }

    if (kx == BV64_POLY && ky != BV64_CONSTANT) {
      return bvpoly64_is_const_plus_var(bvpoly64_term_desc(tbl, x), y);
    }

    if (ky == BV64_POLY && kx != BV64_CONSTANT) {
      return bvpoly64_is_const_plus_var(bvpoly64_term_desc(tbl, y), x);
    }

  }

  return false;
}


/*
 * x and y are two bitvectors of more than 64bits
 */
static bool disequal_bv_terms(term_table_t *tbl, term_t x, term_t y) {
  term_kind_t kx, ky;

  kx = term_kind(tbl, x);
  ky = term_kind(tbl, y);

  if (kx == ky) {
    if (kx == BV_CONSTANT) {
      return x != y;
    }

    if (kx == BV_POLY) {
      return disequal_bvpoly(bvpoly_term_desc(tbl, x), bvpoly_term_desc(tbl, y));
    }

    if (kx == BV_ARRAY) {
      return disequal_bitarrays(bvarray_term_desc(tbl, x), bvarray_term_desc(tbl, y));
    }

  } else {
   
    if (kx == BV_CONSTANT && ky == BV_ARRAY) {
      return disequal_bitarray_bvconst(bvarray_term_desc(tbl, y), bvconst_term_desc(tbl, x));
    }

    if (ky == BV_CONSTANT && kx == BV_ARRAY) {
      return disequal_bitarray_bvconst(bvarray_term_desc(tbl, x), bvconst_term_desc(tbl, y));
    }

    if (kx == BV_POLY && ky != BV_CONSTANT) {
      return bvpoly_is_const_plus_var(bvpoly_term_desc(tbl, x), y);
    }

    if (ky == BV_POLY && kx != BV_CONSTANT) {
      return bvpoly_is_const_plus_var(bvpoly_term_desc(tbl, y), x);
    }

  }

  return false;
}




/*
 * Tuple terms x and y are trivially distinct if they have components 
 * x_i and y_i that are trivially distinct.
 */
static bool disequal_tuple_terms(term_table_t *tbl, term_t x, term_t y) {
  composite_term_t *tuple_x, *tuple_y;
  uint32_t i, n;

  assert(term_type(tbl, x) == term_type(tbl, y));

  tuple_x = tuple_term_desc(tbl, x);
  tuple_y = tuple_term_desc(tbl, y);

  n = tuple_x->arity;
  assert(n == tuple_y->arity);
  for (i=0; i<n; i++) {
    if (disequal_terms(tbl, tuple_x->arg[i], tuple_y->arg[i])) {
      return true;
    }
  }
  return false;
}


/*
 * (update f x1 ... xn a) is trivially distinct from (update f x1 ... xn b)
 * if a is trivially distinct from b.
 */
static bool disequal_update_terms(term_table_t *tbl, term_t x, term_t y) {
  composite_term_t *update_x, *update_y;
  int32_t i, n;

  assert(term_type(tbl, x) == term_type(tbl, y));

  update_x = update_term_desc(tbl, x);
  update_y = update_term_desc(tbl, y);

  n = update_x->arity;
  assert(n == update_y->arity && n > 0);
  for (i=0; i<n-1; i++) {
    if (update_x->arg[i] != update_y->arg[i]) return false;
  }

  return disequal_terms(tbl, update_x->arg[i], update_y->arg[i]);
}


/*
 * Top level check: x and y must be valid terms of compatible types
 */
bool disequal_terms(term_table_t *tbl, term_t x, term_t y) {
  term_kind_t kind;

  if (is_boolean_term(tbl, x)) {
    assert(is_boolean_term(tbl, y));
    return disequal_boolean_terms(x, y);
  }

  if (is_arithmetic_term(tbl, x)) {
    assert(is_arithmetic_term(tbl, y));
    return disequal_arith_terms(tbl, x, y);
  }

  if (is_bitvector_term(tbl, x)) {
    assert(is_bitvector_term(tbl, y) && term_bitsize(tbl, x) == term_bitsize(tbl, y));
    if (term_bitsize(tbl, x) <= 64) {
      return disequal_bv64_terms(tbl, x, y);
    } else {
      return disequal_bv_terms(tbl, x, y);
    }
  }

  kind = term_kind(tbl, x);
  if (kind != term_kind(tbl, y)) return false;

  switch (kind) {
  case CONSTANT_TERM:
    return disequal_constant_terms(x, y);
  case TUPLE_TERM:
    return disequal_tuple_terms(tbl, x, y);
  case UPDATE_TERM:
    return disequal_update_terms(tbl, x, y);
  default:
    return false;
  }
}



// check whether a[i] cannot be equal to b[i] for one i
bool disequal_term_arrays(term_table_t *tbl, uint32_t n, term_t *a, term_t *b) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (disequal_terms(tbl, a[i], b[i])) return true;
  }

  return false;
}

// check whether all elements of a are disequal
// this is expensive: quadratic cost, but should fail quickly on most examples
bool pairwise_disequal_terms(term_table_t *tbl, uint32_t n, term_t *a) {
  uint32_t i, j;

  for (i=0; i<n; i++) {
    for (j=i+1; j<n; j++) {
      if (! disequal_terms(tbl, a[i], a[j])) return false;
    }
  }

  return true;
}




/*******************************
 *  BOUNDS ON BITVECTOR TERMS  *
 ******************************/

/*
 * Copy a bitvector constant a into c
 */
static inline void copy_bvconst_term(bvconst_term_t *a, bvconstant_t *c) {
  assert(a->bitsize > 0);
  bvconstant_copy(c, a->bitsize, a->data);
}

static void copy_bvconst64_term(bvconst64_term_t *a, bvconstant_t *c) {
  uint32_t aux[2];


  aux[0] = (uint32_t) a->value; // lower-order word
  aux[1] = (uint32_t) (a->value >> 32); // high order word  (unused if bitsize <= 32)
  bvconstant_copy(c, a->bitsize, aux);
}


/*
 * Upper bound on t, interpreted as an unsigned integer
 * - copy the result in c
 */
void upper_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_upper_bound_unsigned(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    bvconstant_set_all_one(c, n);
    break;
  }  
}



/*
 * Lower bound on t, interpreted as an unsigned integer
 * - copy the result in c
 */
void lower_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_lower_bound_unsigned(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    bvconstant_set_all_zero(c, n);
    break;
  }  
}


/*
 * Upper bound on t, interpreted as a signed integer
 * - copy the result in c
 */
void upper_bound_signed(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_upper_bound_signed(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    assert(n > 0);
    bvconstant_set_all_one(c, n);
    bvconst_clr_bit(c->data, n-1); // clear the sign bit
    break;
  }  
}


/*
 * Lower bound on t, interpreted as a signed integer
 * - copy the result in c
 */
void lower_bound_signed(term_table_t *tbl, term_t t, bvconstant_t *c) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    copy_bvconst64_term(bvconst64_term_desc(tbl, t), c);
    break;

  case BV_CONSTANT:
    copy_bvconst_term(bvconst_term_desc(tbl, t), c);
    break;

  case BV_ARRAY:
    bitarray_lower_bound_signed(bvarray_term_desc(tbl, t), c);
    break;

  default:
    n = term_bitsize(tbl, t);
    assert(n > 0);
    bvconstant_set_all_zero(c, n);
    bvconst_set_bit(c->data, n-1); // set the sign bit
    break;
  }  
}




/*
 * BOUNDS FOR VECTORS OF 1 TO 64 BITS
 */

/*
 * Upper bound on t, interpreted as an unsigned integer
 */
uint64_t upper_bound_unsigned64(term_table_t *tbl, term_t t) {
  uint64_t c;
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    break;

  case BV_ARRAY:
    c = bitarray_upper_bound_unsigned64(bvarray_term_desc(tbl, t));
    break;

  default:
    n = term_bitsize(tbl, t);
    assert(1 <= n && n <= 64);
    c = mask64(n);
    break;
  }

  return c;
}


/*
 * Lower bound on t, interpreted as an unsigned integer
 */
uint64_t lower_bound_unsigned64(term_table_t *tbl, term_t t) {
  uint64_t c;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    break;

  case BV_ARRAY:
    c = bitarray_lower_bound_unsigned64(bvarray_term_desc(tbl, t));
    break;

  default:
    c = 0;
    break;
  }

  return c;
}


/*
 * Upper bound on t, interpreted as a signed integer
 */ 
uint64_t upper_bound_signed64(term_table_t *tbl, term_t t) {
  uint64_t c;
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    break;

  case BV_ARRAY:
    c = bitarray_upper_bound_signed64(bvarray_term_desc(tbl, t));
    break;

  default:
    n = term_bitsize(tbl, t);
    c = max_signed64(n);
    break;
  }

  return c;
}


/*
 * Lower bound on t, interpreted as a signed integer
 */
uint64_t lower_bound_signed64(term_table_t *tbl, term_t t) {
  uint64_t c;
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    break;

  case BV_ARRAY:
    c = bitarray_lower_bound_signed64(bvarray_term_desc(tbl, t));
    break;

  default:
    n = term_bitsize(tbl, t);
    c = min_signed64(n);
    break;
  }

  return c;
}

