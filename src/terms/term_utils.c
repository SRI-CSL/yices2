/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * UTILITIES FOR SIMPLIFYING TERMS
 */


#include <assert.h>

#include "terms/bv64_constants.h"
#include "terms/term_utils.h"
#include "utils/int_array_sort.h"
#include "utils/int_hash_sets.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"



/*****************************************
 *  INTERVAL ABSTRACTION FOR BITVECTORS  *
 ****************************************/

/*
 * Compute the abstraction of t^d then multiply a by that
 * - the result is stored in a
 * - returned value: true means that a has some information
 *   (i.e., more precise than the full abstraction for n bits)
 * - if the returned value is false, then the default abstraction
 *   is copied in a
 */
static bool bv64_mulpower_abs(term_table_t *tbl, term_t t, uint32_t d, uint32_t n, bv64_abs_t *a) {
  bv64_abs_t aux;
  bool nontrivial;

  assert(is_bitvector_term(tbl, t) && n == term_bitsize(tbl, t));
  assert(1 <= n && n <= 64 && d >= 1);

  bv64_abstract_term(tbl, t, &aux);
  nontrivial = bv64_abs_nontrivial(&aux, n);
  if (d>1 && nontrivial) {
    bv64_abs_power(&aux, d);
    nontrivial = bv64_abs_nontrivial(&aux, n);
  }
  if (nontrivial) {
    bv64_abs_mul(a, &aux);
    nontrivial = bv64_abs_nontrivial(a, n);
  }
  if (!nontrivial) {
    bv64_abs_default(a, n);
  }

  return nontrivial;
}


/*
 * Compute the abstraction of c * t then add that to a
 * - store the result in a
 * - return true is the result has some information (more
 *   precise than the full abstraction for n bits)
 * - return false otherwise and set a to the default 
 *   abstraction for n bits
 */
static bool bv64_addmul_abs(term_table_t *tbl, term_t t, uint64_t c, uint32_t n, bv64_abs_t *a) {
  bv64_abs_t aux;
  bool nontrivial;

  assert(is_bitvector_term(tbl, t) && n == term_bitsize(tbl, t));
  assert(1 <= n && n <= 64 && c == norm64(c, n));

  bv64_abstract_term(tbl, t, &aux);
  nontrivial = bv64_abs_nontrivial(&aux, n);
  if (c != 1 && nontrivial) {
    bv64_abs_mul_const(&aux, c, n);
    nontrivial = bv64_abs_nontrivial(&aux, n);
  }
  if (nontrivial) {
    bv64_abs_add(a, &aux);
    nontrivial = bv64_abs_nontrivial(a, n);
  }
  if (!nontrivial) {
    bv64_abs_default(a, n);
  }

  return nontrivial;
}


/*
 * Abstraction for a power product
 * - stops as soon as the abstraction is too imprecise
 * - nbits = number of bits
 *
 * NOTE: we assume that no term in the power product is zero.
 */
void bv64_abs_pprod(term_table_t *tbl, pprod_t *p, uint32_t nbits, bv64_abs_t *a) {
  uint32_t i, n;

  bv64_abs_one(a);

  n = p->len;
  for (i=0; i<n; i++) {
    if (!bv64_mulpower_abs(tbl, p->prod[i].var, p->prod[i].exp, nbits, a)) {
      break;
    }
  }
}


/*
 * Abstraction for a polynomial
 * - stops as soon as the abstraction is too imprecise
 * - nbits = number of bits
 */
void bv64_abs_poly(term_table_t *tbl, bvpoly64_t *p, uint32_t nbits, bv64_abs_t *a) {
  uint32_t i, n;

  assert(p->bitsize == nbits);

  n = p->nterms;
  i = 0;
  if (p->mono[i].var == const_idx) {
    bv64_abs_constant(a, p->mono[i].coeff, nbits);
    i ++;
  } else {
    bv64_abs_zero(a);
  }

  while (i < n) {
    if (!bv64_addmul_abs(tbl, p->mono[i].var, p->mono[i].coeff, nbits, a)) {
      break;
    }
    i ++;
  }
}


/*
 * Interval abstraction of a bitvector term t
 * - t must be of type (bitvector n) with n <= 64
 * - the result is stored in *a
 */
void bv64_abstract_term(term_table_t *tbl, term_t t, bv64_abs_t *a) {
  uint32_t n;  

  assert(is_bitvector_term(tbl, t));

  n = term_bitsize(tbl, t);
  assert(1 <= n && n <= 64);

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    assert(bvconst64_term_desc(tbl, t)->bitsize == n);
    bv64_abs_constant(a, bvconst64_term_desc(tbl, t)->value, n);
    break;

  case BV_ARRAY:
    assert(bvarray_term_desc(tbl, t)->arity == n);
    bv64_abs_array(a, false_term, bvarray_term_desc(tbl, t)->arg, n);
    break;

  case POWER_PRODUCT:
    bv64_abs_pprod(tbl, pprod_term_desc(tbl, t), n, a);
    break;

  case BV64_POLY:
    bv64_abs_poly(tbl, bvpoly64_term_desc(tbl, t), n, a);
    break;

  default:
    bv64_abs_default(a, n);
    break;
  }
}




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
 * Find the number significant bits of a (in 2s complement)
 * - returns m if a is the sign-extension of a smaller b of m bits
 *   or n otherwise
 * - a is an array of n Boolean terms
 * - a[n-1] is the sign bit
 * - this searches for the largest m <= n such that a[m-1] is not equal to a[n-1].
 */
static uint32_t bitarray_significant_bits(composite_term_t *a) {
  uint32_t n;
  term_t sign;

  assert(a->arity > 0);

  n = a->arity - 1;
  sign = a->arg[n]; // sign bit
  while (n > 0) {
    if (a->arg[n - 1] != sign) break;
    n --;
  }
  return n + 1;
}


/*
 * Upper/lower bound on a bitarray interpreted as a signed integer.
 * - a is an array of n bits. 
 * - Let m be the number of significant bits in a, then we have
 *   1 <= m <= n
 *   bits a[m-1] .... a[n-1] are all equal (sign extension)
 *   a = a[0] + 2 a[1] + ... + 2^(m-2) a[m-2] - 2^(m-1) a[m-1]
 *
 * upper bound:
 *   for i=0 to m-2, replace a[i] by 1 if a[i] != 0
 *   for i=m-1 to n-1, replace a[i] by 0 unless a[i] = 1.
 *
 * lower bound:
 *   for i=0 to m-2, replace a[i] by 0 if a[i] != 1
 *   for i=m-1 to n-1, replace a[i] by 1 unless a[i] = 0.
 */
static void bitarray_upper_bound_signed(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n, m;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_one(c, n);

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == false_term) {
      bvconst_clr_bit(c->data, i);
    }
  }

  // all bits from a->arg[i] to a->arg[n-1] are the same
  if (a->arg[i] != true_term) {
    while (i < n) {
      bvconst_clr_bit(c->data, i);
      i ++;
    }
  }
}


static void bitarray_lower_bound_signed(composite_term_t *a, bvconstant_t *c) {
  uint32_t i, n, m;

  assert(a->arity > 0);

  n = a->arity;
  bvconstant_set_all_zero(c, n);

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == true_term) {
      bvconst_set_bit(c->data, i);
    }
  }

  // all bits from a->arg[i] to a->arg[n-1] are the same
  if (a->arg[i] != false_term) {
    while (i < n) {
      bvconst_set_bit(c->data, i);
      i ++;
    }
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


#if 0

/*
 * Upper/lower bound on a bitarray interpreted as a signed integer.
 *   a = a[0] + 2 a[1] + ... + 2^(n-2) a[n-2] - 2^(n-1) a[m-1]
 *   where m = number of significant bits in a.
 *
 * upper bound:
 *   for i=0 to m-2, replace a[i] by 1 if a[i] != 0
 *   for i=m-1 to n-1, replace a[i] by 0 unless a[i] = 1.
 *
 * lower bound:
 *   for i=0 to m-2, replace a[i] by 0 if a[i] != 1
 *   for i=m-1 to n-1, replace a[i] by 1 unless a[i] = 0.
 */
static uint64_t bitarray_upper_bound_signed64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n, m;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = mask64(n); // c = 0001...1

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == false_term) {
      c = clr_bit64(c, i);
    }
  }

  // i is equal to m-1
  // All bits from a->arg[m-1] to a->arg[n-1] are the same
  if (a->arg[i] != true_term) {
    while (i < n) {
      c = clr_bit64(c, i);
      i ++;
    }
  }

  assert(c == norm64(c, n));

  return c;
}


static uint64_t bitarray_lower_bound_signed64(composite_term_t *a) {
  uint64_t c;
  uint32_t i, n, m;

  assert(0 < a->arity && a->arity <= 64);

  n = a->arity;
  c = 0;

  m = bitarray_significant_bits(a);
  assert(0 < m && m <= n);

  for (i=0; i<m-1; i++) {
    if (a->arg[i] == true_term) {
      c = set_bit64(c, i);
    }
  }

  // i is equal to m-1.
  // All bits from a->arg[m-1] to a->arg[n-1] are the same
  if (a->arg[i] != false_term) {
    while (i < n) {
      c = set_bit64(c, i);
      i ++;
    }
  }

  assert(c == norm64(c, n));


  return c;
}

#endif


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
 * Generic form for two bitvector terms x and y
 */
bool disequal_bitvector_terms(term_table_t *tbl, term_t x, term_t y) {
  assert(is_bitvector_term(tbl, x) && is_bitvector_term(tbl, y) &&
         term_bitsize(tbl, x) == term_bitsize(tbl, y));

  if (term_bitsize(tbl, x) <= 64) {
    return disequal_bv64_terms(tbl, x, y);
  } else {
    return disequal_bv_terms(tbl, x, y);
  }
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
  default:
    return false;
  }
}



// check whether a[i] cannot be equal to b[i] for one i
bool disequal_term_arrays(term_table_t *tbl, uint32_t n, const term_t *a, const term_t *b) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (disequal_terms(tbl, a[i], b[i])) return true;
  }

  return false;
}

// check whether all elements of a are disequal
// this is expensive: quadratic cost, but should fail quickly on most examples
bool pairwise_disequal_terms(term_table_t *tbl, uint32_t n, const term_t *a) {
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
  bv64_abs_t abs;
  uint64_t c;
  uint32_t n;

  bv64_abstract_term(tbl, t, &abs);
  n = term_bitsize(tbl, t);
  c = norm64((uint64_t) abs.high, n); // upper bound

  return c;
}


/*
 * Lower bound on t, interpreted as a signed integer
 */
uint64_t lower_bound_signed64(term_table_t *tbl, term_t t) {
  bv64_abs_t abs;
  uint64_t c;
  uint32_t n;

  bv64_abstract_term(tbl, t, &abs);
  n = term_bitsize(tbl, t);
  c = norm64((uint64_t) abs.low, n); // lower bound

  return c;
}


/******************************************************
 *  MINIMAL/MAXIMAL SIGNED/UNSIGNED BITVECTOR VALUES  *
 *****************************************************/

bool bvterm_is_zero(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    return bvconst64_term_desc(tbl, t)->value == 0;

  case BV_CONSTANT:
    n = (term_bitsize(tbl, t) + 31) >> 5; // number of words
    return bvconst_is_zero(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}

bool bvterm_is_minus_one(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst64_is_minus_one(bvconst64_term_desc(tbl, t)->value, n);

  case BV_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst_is_minus_one(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}

bool bvterm_is_min_signed(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst64_term_desc(tbl, t)->value == min_signed64(n);

  case BV_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst_is_min_signed(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}

bool bvterm_is_max_signed(term_table_t *tbl, term_t t) {
  uint32_t n;

  assert(is_bitvector_term(tbl, t));

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst64_term_desc(tbl, t)->value == max_signed64(n);

  case BV_CONSTANT:
    n = term_bitsize(tbl, t);
    return bvconst_is_max_signed(bvconst_term_desc(tbl, t)->data, n);

  default:
    return false;
  }
}



/*****************************************
 *  SIMPLIFICATION OF BIT-VECTOR TERMS   *
 ****************************************/

/*
 * Get bit i of term t:
 * - return NULL_TERM if the bit can't be determined
 * - return true or false if t is a bitvector constant
 * - return b_i if t is (bv-array b_0 .. b_i ...)
 *
 * t must be a bitvector term of size > i
 */
term_t extract_bit(term_table_t *tbl, term_t t, uint32_t i) {
  uint32_t *d;
  uint64_t c;
  term_t bit;

  assert(is_bitvector_term(tbl, t) && term_bitsize(tbl, t) > i);

  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    c = bvconst64_term_desc(tbl, t)->value;
    bit = bool2term(tst_bit64(c, i));
    break;

  case BV_CONSTANT:
    d = bvconst_term_desc(tbl, t)->data;
    bit = bool2term(bvconst_tst_bit(d, i));
    break;

  case BV_ARRAY:
    bit = bvarray_term_desc(tbl, t)->arg[i];
    break;

  default:
    bit = NULL_TERM;
    break;
  }

  return bit;
}




/*
 * Check whether (eq b c) simplifies and if so returns the result.
 * - b and c must be boolean terms (assumed not opposite of each other).
 * - return NULL_TERM if no simplification is found
 *
 * Rules:
 *   (eq b b)     --> true
 *   (eq b true)  --> b
 *   (eq b false) --> (not b)
 * + symmetric cases for the last two rules
 */
static term_t check_biteq_simplifies(term_t b, term_t c) {
  assert(! opposite_bool_terms(b, c));

  if (b == c) return true_term;

  if (b == true_term)  return c;
  if (b == false_term) return opposite_term(c); // not c
  if (c == true_term)  return b;
  if (c == false_term) return opposite_term(b);

  return NULL_TERM;
}


/*
 * Check whether (and a (eq b c)) simplifies and, if so, returns the result.
 * - a, b, and c are three boolean terms.
 * - return NULL_TERM if no cheap simplification is found
 *
 * We assume that the cheaper simplification tests have been tried before:
 * (i.e., we assume a != false and  b != (not c)).
 */
static term_t check_accu_biteq_simplifies(term_t a, term_t b, term_t c) {
  term_t eq;


  // first check whether (eq b c) simplifies
  eq = check_biteq_simplifies(b, c);
  if (eq == NULL_TERM) return NULL_TERM;

  /*
   * try to simplify (and a eq)
   */
  assert(a != false_term && eq != false_term);

  if (a == eq) return a;
  if (opposite_bool_terms(a, eq)) return false_term;

  if (a == true_term) return eq;
  if (eq == true_term) return a;

  return NULL_TERM;
}



/*
 * Check whether (bveq u v) simplifies:
 * - u is a bitvector constant of no more than 64 bits
 * - v is a bv_array term
 *
 * Return NULL_TERM if no cheap simplification is found.
 */
static term_t check_eq_bvconst64(bvconst64_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t accu, b;

  n = u->bitsize;
  assert(n == v->arity);
  accu = true_term;

  for (i=0; i<n; i++) {
    b = bool2term(tst_bit64(u->value, i)); // bit i of u
    accu = check_accu_biteq_simplifies(accu, b, v->arg[i]);
    if (accu == NULL_TERM || accu == false_term) {
      break;
    }
  }

  return accu;
}


/*
 * Same thing for a generic constant u.
 */
static term_t check_eq_bvconst(bvconst_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t accu, b;

  n = u->bitsize;
  assert(n == v->arity);
  accu = true_term;

  for (i=0; i<n; i++) {
    b = bool2term(bvconst_tst_bit(u->data, i)); // bit i of u
    accu = check_accu_biteq_simplifies(accu, b, v->arg[i]);
    if (accu == NULL_TERM || accu == false_term) {
      break;
    }
  }

  return accu;
}


/*
 * Same thing for two bv_array terms
 */
static term_t check_eq_bvarray(composite_term_t *u, composite_term_t *v) {
  uint32_t i, n;
  term_t accu;

  n = u->arity;
  assert(n == v->arity);
  accu = true_term;

  for (i=0; i<n; i++) {
    accu = check_accu_biteq_simplifies(accu, u->arg[i], v->arg[i]);
    if (accu == NULL_TERM || accu == false_term) {
      break;
    }
  }

  return accu;
}



/*
 * Try to simplify (bv-eq t1 t2) to a boolean term
 * - if t1 and t2 can be rewritten as arrays of bits
 *   [b0 .. b_n] and [c_0 ... c_n], respectively,
 *   then the function checks whether
 *      (and (b0 == c0) ... (b_n == c_n))
 *   simplifies to a single boolean term.
 * - return NULL_TERM if no simplification is found
 */
term_t simplify_bveq(term_table_t *tbl, term_t t1, term_t t2) {
  term_kind_t k1, k2;
  term_t aux;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2) &&
         term_bitsize(tbl, t1) == term_bitsize(tbl, t2));

  k1 = term_kind(tbl, t1);
  k2 = term_kind(tbl, t2);
  aux = NULL_TERM;
  switch (k1) {
  case BV64_CONSTANT:
    if (k2 == BV_ARRAY) {
      aux = check_eq_bvconst64(bvconst64_term_desc(tbl, t1), bvarray_term_desc(tbl, t2));
    }
    break;

  case BV_CONSTANT:
    if (k2 == BV_ARRAY) {
      aux = check_eq_bvconst(bvconst_term_desc(tbl, t1), bvarray_term_desc(tbl, t2));
    }
    break;

  case BV_ARRAY:
    if (k2 == BV64_CONSTANT) {
      aux = check_eq_bvconst64(bvconst64_term_desc(tbl, t2), bvarray_term_desc(tbl, t1));
    } else if (k2 == BV_CONSTANT) {
      aux = check_eq_bvconst(bvconst_term_desc(tbl, t2), bvarray_term_desc(tbl, t1));
    } else if (k2 == BV_ARRAY) {
      aux = check_eq_bvarray(bvarray_term_desc(tbl, t1), bvarray_term_desc(tbl, t2));
    }
    break;

  default:
    break;
  }


  return aux;
}



/*
 * Convert (bveq u v) to a conjunction of boolean terms
 * - u is a BV64 constant, v is a bitarray
 * - store the result in vector a
 */
static void flatten_eq_bvconst64(bvconst64_term_t *u, composite_term_t *v, ivector_t *a) {
  uint32_t i, n;
  term_t aux, b;

  n = u->bitsize;
  assert(n == v->arity);
  for (i=0; i<n; i++) {
    b = bool2term(tst_bit64(u->value, i)); // bit i of u
    aux = check_biteq_simplifies(b, v->arg[i]);
    assert(aux != NULL_TERM);

    if (aux != true_term) {
      ivector_push(a, aux);
    }
  }
}


/*
 * Same thing when u is a BV constant and v is a bitarray
 */
static void flatten_eq_bvconst(bvconst_term_t *u, composite_term_t *v, ivector_t *a) {
  uint32_t i, n;
  term_t aux, b;

  n = u->bitsize;
  assert(n == v->arity);
  for (i=0; i<n; i++) {
    b = bool2term(bvconst_tst_bit(u->data, i)); // bit i of u
    aux = check_biteq_simplifies(b, v->arg[i]);
    assert(aux != NULL_TERM);

    if (aux != true_term) {
      ivector_push(a, aux);
    }
  }
}


/*
 * Try to convert (bveq u v) to a conjunction of Boolean terms
 * - u and v are bit arrays of the same size
 * - return true if that succeeds
 */
static bool flatten_eq_bvarray(composite_term_t *u, composite_term_t *v, ivector_t *a) {
  uint32_t i, n;
  term_t aux;

  n = u->arity;
  assert(n == v->arity);
  for (i=0; i<n; i++) {
    aux = check_biteq_simplifies(u->arg[i], v->arg[i]);
    if (aux == NULL_TERM) return false; // failed
    if (aux != true_term) {
      ivector_push(a, aux);
    }
  }

  return true;
}



/*
 * Try to simplify (bv-eq t1 t2) to a conjunction of terms
 * - if t1 and t2 can be rewritten as arrays of bits
 *   [b_0 ... b_n] and [c_0 ... c_n], respectively,
 *   then the function checks whether each
 *   equality (b_i == c_i)  simplifies to a single Boolean term e_i
 * - if all of them do, then the function
 *   returns true and adds e_0, ... e_n to vector v
 *
 * As above: t1 and t2 must not be equal, and disequal_bitvector_terms(tbl, t1, t2)
 * must be false.
 */
bool bveq_flattens(term_table_t *tbl, term_t t1, term_t t2, ivector_t *v) {
  term_kind_t k1, k2;

  assert(is_bitvector_term(tbl, t1) && is_bitvector_term(tbl, t2) &&
         term_bitsize(tbl, t1) == term_bitsize(tbl, t2));

  k1 = term_kind(tbl, t1);
  k2 = term_kind(tbl, t2);
  switch (k1) {
  case BV64_CONSTANT:
    if (k2 == BV_ARRAY) {
      flatten_eq_bvconst64(bvconst64_term_desc(tbl, t1), bvarray_term_desc(tbl, t2), v);
      return true;
    }
    break;

  case BV_CONSTANT:
    if (k2 == BV_ARRAY) {
      flatten_eq_bvconst(bvconst_term_desc(tbl, t1), bvarray_term_desc(tbl, t2), v);
      return true;
    }
    break;

  case BV_ARRAY:
    if (k2 == BV64_CONSTANT) {
      flatten_eq_bvconst64(bvconst64_term_desc(tbl, t2), bvarray_term_desc(tbl, t1), v);
      return true;
    } else if (k2 == BV_CONSTANT) {
      flatten_eq_bvconst(bvconst_term_desc(tbl, t2), bvarray_term_desc(tbl, t1), v);
      return true;
    } else if (k2 == BV_ARRAY) {
      return flatten_eq_bvarray(bvarray_term_desc(tbl, t1), bvarray_term_desc(tbl, t2), v);
    }
    break;

  default:
    break;
  }

  return false;
}


/******************
 *  SUBSUMPTION   *
 *****************/

/*
 * Check whether two bitvector literals t1 and t2 are incompatible
 * MORE TO BE DONE
 */
bool incompatible_bitvector_literals(term_table_t *tbl, term_t t1, term_t t2) {
  composite_term_t *eq1, *eq2;
  bool result;
  uint32_t i, j;

  if (opposite_bool_terms(t1, t2)) {
    result = true;
  } else {
    result = false;

    if (is_pos_term(t1) && is_pos_term(t2) &&
	term_kind(tbl, t1) == BV_EQ_ATOM && term_kind(tbl, t2) == BV_EQ_ATOM) {
      eq1 = bveq_atom_desc(tbl, t1);
      eq2 = bveq_atom_desc(tbl, t2);
      assert(eq1->arity == 2 && eq2->arity == 2);

      for (i=0; i<2; i++) {
	for (j=0; j<2; j++) {
	  if (eq1->arg[i] == eq2->arg[j]) {
	    result = disequal_bv_terms(tbl, eq1->arg[1 - i], eq2->arg[1 - j]);
	    goto done;
	  }
	}
      }
    }
  }

 done:
  return result;
}


/*
 * Check whether two Boolean terms t1 and t2
 * are incompatible (i.e., (t1 and t2) is false.
 * - this does very simple checks for now
 */
bool incompatible_boolean_terms(term_table_t *tbl, term_t t1, term_t t2) {
  composite_term_t *eq1, *eq2;
  uint32_t i, j;

  if (is_bitvector_literal(tbl, t1) && is_bitvector_literal(tbl, t2)) {
    return incompatible_bitvector_literals(tbl, t1, t2);
  }

  if (t1 == false_term || t2 == false_term || opposite_bool_terms(t1, t2)) {
    return true;
  }

  if (is_pos_term(t1) && is_pos_term(t2) &&
      term_kind(tbl, t1) == EQ_TERM && term_kind(tbl, t2) == EQ_TERM) {
    eq1 = eq_term_desc(tbl, t1);
    eq2 = eq_term_desc(tbl, t2);

    for (i=0; i<2; i++) {
      for (j=0; j<2; j++) {
	if (eq1->arg[i] == eq2->arg[j]) {
	  return disequal_bv_terms(tbl, eq1->arg[1 - i], eq2->arg[1 - j]);
	}
      }
    }
  }

  return false;
}


/*
 * Check whether t1 subsumes t2 (i.e., t1 => t2)
 */
bool term_subsumes_term(term_table_t *tbl, term_t t1, term_t t2) {
  return incompatible_boolean_terms(tbl, t1, opposite_term(t2));
}

/*
 * Check whether t1 subsumes all elements of a[0 ... n-1]
 */
bool term_subsumes_array(term_table_t *tbl, term_t t1, uint32_t n, term_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (!term_subsumes_term(tbl, t1, a[i])) {
      return false;
    }
  }

  return true;
}





/****************************
 *  EQUALITY DECOMPOSITION  *
 ***************************/

/*
 * Check whether t is equivalent to (x == a) where x is a term and a is a constant
 * - if so stores the term and constant in *x and *a, and returns true.
 * - otherwise returns false, and leave *x and *a unchanged.
 */
bool is_term_eq_const(term_table_t *tbl, term_t t, term_t *x, term_t *a) {
  composite_term_t *eq;

  assert(good_term(tbl, t));
  if (is_pos_term(t)) {
    switch (term_kind(tbl, t)) {
    case EQ_TERM:
    case BV_EQ_ATOM:
      eq = composite_term_desc(tbl, t);
      assert(eq->arity == 2);
      if (is_const_term(tbl, eq->arg[0])) {
	*a = eq->arg[0];
	*x = eq->arg[1];
	return true;
      }
      if (is_const_term(tbl, eq->arg[1])) {
	*x = eq->arg[0];
	*a = eq->arg[1];
	return true;
      }
      break;

    default:
      break;
    }

  }

  return false;
}



/*
 * Variant: check whether t is of the form (x == a) where x is uninterpreted and
 * a is a constant.
 */
bool is_unint_eq_const(term_table_t *tbl, term_t t, term_t *x, term_t *a) {
  term_t x0, a0;

  if (is_term_eq_const(tbl, t, &x0, &a0) &&
      term_kind(tbl, x0) == UNINTERPRETED_TERM) {
    assert(is_pos_term(x0));
    *x = x0;
    *a = a0;
    return true;
  }

  return false;
}



