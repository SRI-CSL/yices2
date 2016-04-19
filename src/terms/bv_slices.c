/*
 * The Yices SMT Solver. Copyright 2016 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SLICES IN AN ARRAY OF BITS
 */

#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"
#include "terms/bv_slices.h"
#include "utils/memalloc.h"


/*
 * Initialize a bvslicer vector
 * - nothing is allocated yet.
 */
void init_bvslicer(bvslicer_t *slicer) {
  slicer->data = NULL;
  slicer->nelems = 0;
  slicer->size = 0;
  init_ivector(&slicer->buffer, 0);
}


/*
 * Free slice: delete the bvconstant if any
 */
static void delete_bvslice(bvslice_t *s) {
  if (s->tag == BVSLICE_CONST) {
    safe_free(s->desc.c.value);
    s->desc.c.value = NULL;
  }
}


/*
 * Reset to the empty vector
 */
void reset_bvslicer(bvslicer_t *slicer) {
  uint32_t i, n;

  n = slicer->nelems;
  for (i=0; i<n; i++) {
    delete_bvslice(slicer->data + i);
  }
  slicer->nelems = 0;
  ivector_reset(&slicer->buffer);
}


/*
 * Delete: free memory
 */
void delete_bvslicer(bvslicer_t *slicer) {
  uint32_t i, n;

  n = slicer->nelems;
  for (i=0; i<n; i++) {
    delete_bvslice(slicer->data + i);
  }
  safe_free(slicer->data);
  slicer->data = NULL;
  delete_ivector(&slicer->buffer);
}


/*
 * Allocate/extend slicer
 */
static void extend_bvslicer(bvslicer_t *slicer) {
  uint32_t n, new_size;

  n = slicer->size;
  if (n == 0) {
    new_size = DEF_BVSLICER_SIZE;
    assert(new_size <= MAX_BVSLICER_SIZE);
    slicer->data = (bvslice_t *) safe_malloc(new_size * sizeof(bvslice_t));
    slicer->size = new_size;
  } else {
    new_size = n + (n>>1); // arount 50% larger
    if (new_size > MAX_BVSLICER_SIZE) {
      out_of_memory();
    }
    slicer->data = (bvslice_t *) safe_realloc(slicer->data, new_size * sizeof(bvslice_t));
    slicer->size = new_size;
  }  
}

static uint32_t bvslicer_new(bvslicer_t *slicer) {
  uint32_t i;

  i = slicer->nelems;
  slicer->nelems = i + 1;
  if (i == slicer->size) {
    extend_bvslicer(slicer);
  }
  assert(i < slicer->size);
  return i;
}

/*
 * Add a slice descriptor at the end of slicer
 */
static void bvslicer_add_repeat(bvslicer_t *slicer, term_t bit, uint32_t count) {
  uint32_t i;

  i = bvslicer_new(slicer);
  slicer->data[i].tag = BVSLICE_REPEAT;
  slicer->data[i].desc.r.bit = bit;
  slicer->data[i].desc.r.count = count;
}

static void bvslicer_add_extract(bvslicer_t *slicer, term_t v, uint32_t l, uint32_t h) {
  uint32_t i;

  assert(l <= h);

  i = bvslicer_new(slicer);
  slicer->data[i].tag = BVSLICE_EXTRACT;
  slicer->data[i].desc.e.vector = v;
  slicer->data[i].desc.e.low = l;
  slicer->data[i].desc.e.high = h;
}

// constant v of n bits. v must be normalized, n must be at most 64
static void bvslicer_add_const64(bvslicer_t *slicer, uint64_t v, uint32_t n) {
  uint32_t i;

  assert(v == norm64(v, n));

  i = bvslicer_new(slicer);
  slicer->data[i].tag = BVSLICE_CONST64;
  slicer->data[i].desc.c64.value = v;
  slicer->data[i].desc.c64.nbits = n;
}

// constant of more than 64bits. v must be normalized. n = number of bits
static void bvslicer_add_const(bvslicer_t *slicer, uint32_t *v, uint32_t n) {
  uint32_t i;

  assert(n > 64 && bvconst_is_normalized(v, n));

  i = bvslicer_new(slicer);
  slicer->data[i].tag = BVSLICE_CONST;
  slicer->data[i].desc.c.value = v;
  slicer->data[i].desc.c.nbits = n;
}


/*
 * CONSTANT SLICES
 */

/*
 * Check whether all elements of array a are equal
 * - n = number of elements
 */
static bool constant_array(const term_t *a, uint32_t n) {
  uint32_t i;
  term_t a0;

  assert(n > 0);
  a0 = a[0];
  for (i=1; i<n; i++) {
    if (a[i] != a0) return false;
  }
  return true;
}

/*
 * Convert array a[0... n] to a 64bit constant
 * - all elements a[i] should be either true_term or false_term
 * - a[0] = least significant bit, a[n-1] = most significant bit
 */
static uint64_t bv64_from_array(const term_t *a, uint32_t n) {
  uint64_t c, mask;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = 0;
  mask = 1;
  for (i=0; i<n; i++) {
    c |= mask & (a[i] == true_term);
    mask <<= 1;
  }

  assert(norm64(c, n) == c);

  return c;
}


/*
 * Convert array a[0 ... n] to a bitvector constant.
 * - allocate an array w of (ceil n/32) words and store the constant into w
 */
static uint32_t *bv_from_array(const term_t *a, uint32_t n) {
  uint32_t *v;
  uint32_t i, w;

  w = (n + 31) >> 5; // number of words
  v = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
  for (i=0; i<n; i++) {
    if (a[i] == true_term) {
      bvconst_set_bit(v, i);
    } else {
      assert(a[i] == false_term);
      bvconst_clr_bit(v, i);
    }
  }
  bvconst_normalize(v, n);

  return v;
}

/*
 * Build a slice from an array of constant terms
 * - every element in a[0 ... n-1] must be either true_term or false_term
 * - n must be positive
 * - if all elements are equal: add [repeat n a[0]]
 * - otherwise build a constant and add it
 */
static void bvslicer_add_const_array(bvslicer_t *slicer, const term_t *a, uint32_t n) {
  assert(n > 0);

  if (constant_array(a, n)) {
    bvslicer_add_repeat(slicer, a[0], n);
  } else if (n <= 64) {
    bvslicer_add_const64(slicer, bv64_from_array(a, n), n);
  } else {
    bvslicer_add_const(slicer, bv_from_array(a, n), n);
  }
}


/*
 * Scan a[i ... n-1] from the left until a non-constant term is found
 * - must have i <= n
 * - add all constant terms to slicer->buffer
 * - return n if a[i ... n-1] are all constant
 * - otherwise return the smallest j such that a[j] is not a constant 
 */
static inline bool is_bool_constant(term_t t) {
  return index_of(t) == bool_const; // i.e., t is true_term or false_term
}

static uint32_t get_bvconst_prefix(bvslicer_t *slicer, const term_t *a, uint32_t i, uint32_t n) {
  uint32_t j;

  j = i;
  while (j < n && is_bool_constant(a[j])) {
    ivector_push(&slicer->buffer, a[j]);
    j ++;
  }

  return j;
}


/*
 * Scan a[i ... n-1] until a term different from t is found
 * - return n if all a[j] are equal to t (or if i == n)
 * - return the smallest j such that a[j] /= t otherwise
 */
static uint32_t get_repeat_prefix(const term_t *a, term_t t, uint32_t i, uint32_t n) {
  uint32_t j;

  j = i;
  while (j < n && a[j] == t) {
    j ++;
  }

  return j;
}


/*
 * Check whether x is (bit t k)
 */
static bool is_bit_select(term_table_t *tbl, term_t x, term_t t, term_t k) {
  select_term_t *d;

  if (is_pos_term(x) && term_kind(tbl, x) == BIT_TERM) {
    d = bit_term_desc(tbl, x);
    return d->idx == k && d->arg == t;
  }
  return false;
}

/*
 * Scan a[i ... n-1] for terms of the form (bit t k) ... (bit t k+r)
 */
static uint32_t get_extract_prefix(term_table_t *tbl, const term_t *a, term_t t, uint32_t k, uint32_t i, uint32_t n) {  
  uint32_t j;

  j = i;
  while (j < n && is_bit_select(tbl, a[j], t, k)) {
    j ++;
    k ++;
  }

  return j;
}


/*
 * Search for an useful prefix of a[i ... n] and add it to slicer
 * - must have i < n
 * - returns true if such a prefix is found
 * - returns false otherwise
 * - update *i to point to the first element of a that follows the prefix
 *
 * Useful prefix:
 * - any sequence of true/false terms (i.e., a constant slice)
 * - a repetiton [(bit t k) .... (bit t k)] of length 2 or more
 * - a subvector [(bit t k) ... (bit t k+r)] of length 2 or more
 */
static bool get_prefix(bvslicer_t *slicer, term_table_t *tbl, const term_t *a, uint32_t *i, uint32_t n) {  
  select_term_t *d;
  uint32_t j, k, l;
  term_t t, u;

  j = *i;

  assert(j < n);

  t = a[j];
  if (is_bool_constant(t)) {
    ivector_reset(&slicer->buffer);
    ivector_push(&slicer->buffer, t);
    k = get_bvconst_prefix(slicer, a, j+1, n);
    *i = k;
    assert(k - j == slicer->buffer.size);
    bvslicer_add_const_array(slicer, slicer->buffer.data, slicer->buffer.size);
    return true;
  }

  if (j+1 < n && term_kind(tbl, t) == BIT_TERM) {
    k = get_repeat_prefix(a, t, j+1, n);
    if (k > j+1) { // a[j ... k-1] form a repeat prefix      
      *i = k;
      bvslicer_add_repeat(slicer, t, k - j);
      return true;
    }
    
    d = bit_term_desc(tbl, t);
    l = d->idx;
    u = d->arg;
    k = get_extract_prefix(tbl, a, u, l+1, j+1, n);
    if (k > j + 1) {
      // a[j ... k-1] is a slice
      // a[j] is (bit u l) and a[k-1] is (bit u l+k-j-1)
      *i = k;
      bvslicer_add_extract(slicer, u, l, l+(k-j)-1);
      return true;
    }
  }
  
  return false;
}


/*
 * Process an array of bits a[0 ... n-1]
 * - each element of must be a Boolean term defined in tbl
 * - try to split the array into slices and store the result in slicer
 * - returns true if this succeeds, false otherwise
 */
bool slice_bitarray(bvslicer_t *slicer, term_table_t *tbl, const term_t *a, uint32_t n) {
  uint32_t i;

  reset_bvslicer(slicer);

  i = 0;
  while (i < n) {
    if (! get_prefix(slicer, tbl, a, &i, n)) {
      return false;
    }
  }

  return true;
}


/*
 * PATTERNS
 */
bool is_repeat_zero(bvslice_t *d, uint32_t *r) {
  if (d->tag == BVSLICE_REPEAT && d->desc.r.bit == false_term) {
    *r = d->desc.r.count;
    return true;
  }
  return false;
}

bool is_repeat_one(bvslice_t *d, uint32_t *r) {
  if (d->tag == BVSLICE_REPEAT && d->desc.r.bit == true_term) {
    *r = d->desc.r.count;
    return true;
  }
  return false;
}

/*
 * Check whether array d[0 ... n-1] looks like a (zero-extend u k). If so
 * store the extend count k into *r.
 */
bool is_zero_extend(bvslice_t *d, uint32_t n, uint32_t *r) {
  return n >= 2 && is_repeat_zero(d + n-1, r);
}


/*
 * Check whether d[0 ... n-1] looks like (sign-extend u k). If so,
 * store the extend count k into *r.
 */
bool is_sign_extend(term_table_t *tbl, bvslice_t *d, uint32_t n, uint32_t *r) {
  term_t u, b;
  uint32_t j;
  
  if (n >= 2 && d[n-2].tag == BVSLICE_EXTRACT && d[n-1].tag == BVSLICE_REPEAT) {
    u = d[n-2].desc.e.vector;
    j = d[n-2].desc.e.high; // d[n-2] is (extract u i j) for some i <= j
    b = d[n-1].desc.r.bit;  // d[n-1] is (repeat b k) for some k)
    if (is_bit_select(tbl, b, u, j)) {
      *r = d[n-1].desc.r.count;
      return true;
    }
  }

  return false;
}

