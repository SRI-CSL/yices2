/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Bit-vector constants = finite-precision integers.
 * Constants are represented as fixed-size arrays of 32bit integers
 *
 * These functions are intended to be used for small arrays (128-256 bits at most).
 * For larger sizes, GMP integers should be faster.
 */

#include <stdio.h>
#include <assert.h>
#include <ctype.h>

#include "terms/bv_constants.h"
#include "utils/bit_tricks.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "utils/object_stores.h"


#include "api/yices_thread_local.h"

/*****************
 *  ALLOCATION   *
 ****************/

/*
 * Allocator = array of object_stores
 * - store[0] is unused
 * - store[i] is for vectors of size 2i and (2i - 1)
 *   (the size is measured in number of words)
 *
 * We must ensure that all bitvectors allocated in store[i]
 * have size <= MAX_OBJ_SIZE (i.e., 512 bytes). So we want
 *  2 * i * sizeof(uint32_t) <= MAX_OBJ_SIZE.
 *
 * Bitvectors os size larger than that are allocated via
 * direct calls to malloc/free.
 */
typedef struct {
  object_store_t *store;
  uint32_t nstores;
} bvconst_allocator_t;


/*
 * i < MAX_NUM_STORE ==> 2 i * sizeof(uint32_t) <= MAX_OBJ_SIZE
 */
#define MAX_NUM_STORES ((uint32_t) (1 + (MAX_OBJ_SIZE/(2 * sizeof(uint32_t)))))


/*
 * Block size for each object store = number of bitvectors
 * in each block of the store.
 */
#define BVCONST_BANK_SIZE 128


/*
 * Global allocator  iam: why is this not protected by a lock?
 */
static YICES_THREAD_LOCAL bvconst_allocator_t allocator;


/*
 * Initialize s
 */
static void init_allocator(bvconst_allocator_t *s) {
  s->nstores = 0;
  s->store = NULL;
}

/*
 * Extend allocator to include at least n+1 stores
 */
static void resize_allocator(bvconst_allocator_t *s, uint32_t n) {
  uint32_t new_size, i;

  assert(s->nstores <= n && n < MAX_NUM_STORES);

  // new_size = min(max(s->nstores * 1.5, n+1), MAX_NUM_STORES)
  new_size = s->nstores + 1;
  new_size += new_size >> 1;
  if (new_size <= n) {
    new_size = n + 1;
  } else if (new_size > MAX_NUM_STORES) {
    new_size = MAX_NUM_STORES;
  }

  assert(new_size <= MAX_NUM_STORES && new_size >= n+1);

  s->store = (object_store_t *) safe_realloc(s->store, new_size * sizeof(object_store_t));
  for (i=s->nstores; i<new_size; i++) {
    init_objstore(s->store + i, (2 * i) * sizeof(uint32_t), BVCONST_BANK_SIZE);
  }
  s->nstores = new_size;
}


/*
 * Allocate a  new vector of size k
 */
static uint32_t *alloc_vector(bvconst_allocator_t *s, uint32_t k) {
  object_store_t *m;
  uint32_t *p;
  uint32_t i;

  assert(0 < k && k <= (UINT32_MAX/sizeof(uint32_t)));

  i = ((k + 1) >> 1); // store index for size k
  if (i < MAX_NUM_STORES) {
    if (i >= s->nstores) {
      resize_allocator(s, i);
    }
    m = s->store + i;
    assert(m->objsize >= k * sizeof(uint32_t));
    p = (uint32_t *) objstore_alloc(m);
  } else {
    p = (uint32_t *) safe_malloc(k * sizeof(uint32_t));
  }

  return p;
}


/*
 * Free vector bv of size k
 */
static void free_vector(bvconst_allocator_t *s, uint32_t *bv, uint32_t k) {
  uint32_t i;

  // store index = ceil(k/2)
  i = ((k + 1) >> 1);
  if (i < MAX_NUM_STORES) {
    assert(0 < i && i < s->nstores);
    objstore_free(s->store + i, (void *) bv);
  } else {
    safe_free(bv);
  }
}


/*
 * Delete s: free all stores
 */
static void delete_allocator(bvconst_allocator_t *s) {
  uint32_t i;

  for (i=0; i<s->nstores; i++) {
    delete_objstore(s->store + i);
  }
  safe_free(s->store);
  s->store = NULL;
  s->nstores = 0;
}


/*
 * Initialization: prepare global store
 */
void init_bvconstants(void) {
  init_allocator(&allocator);
}

/*
 * Cleanup: free the store
 */
void cleanup_bvconstants(void) {
  delete_allocator(&allocator);
}

/*
 * Allocate a vector of k words.
 */
uint32_t *bvconst_alloc(uint32_t k) {
  return alloc_vector(&allocator, k);
}

/*
 * Free vector bv of size k.
 */
void bvconst_free(uint32_t *bv, uint32_t k) {
  free_vector(&allocator, bv, k);
}





/****************************
 *  BVCONSTANT STRUCTURES   *
 ***************************/

/*
 * Initialization: bitsize is set to 0
 */
void init_bvconstant(bvconstant_t *b) {
  b->bitsize = 0;
  b->width = 0;
  b->arraysize = 0;
  b->data = NULL;
}

/*
 * Delete: free allocated memory
 */
void delete_bvconstant(bvconstant_t *b) {
  safe_free(b->data);
  b->data = NULL;
}

/*
 * Resize: make the array large enough for n bits
 */
void bvconstant_set_bitsize(bvconstant_t *b, uint32_t n) {
  uint32_t k;

  k = (n + 31) >> 5; // ceil(n/32)
  if (b->arraysize < k) {
    b->data = (uint32_t *) safe_realloc(b->data, k * sizeof(uint32_t));
    b->arraysize = k;
    /*
     * To prevent false alarms from valgrind, just make sure it's
     * all initialized.
     */
    bvconst_clear(b->data, k);
  }
  b->bitsize = n;
  b->width = k;
}


/*
 * Resize and initialize to 0b0....0
 */
void bvconstant_set_all_zero(bvconstant_t *b, uint32_t n) {
  uint32_t k;

  k = (n + 31) >> 5;
  bvconstant_set_bitsize(b, n);
  bvconst_clear(b->data, k);
}


/*
 * Resize and initialize to 0b1....1
 */
void bvconstant_set_all_one(bvconstant_t *b, uint32_t n) {
  uint32_t k;

  k = (n + 31) >> 5;
  bvconstant_set_bitsize(b, n);
  bvconst_set_minus_one(b->data, k);
  bvconst_normalize(b->data, n);
}


/*
 * Resize and copy bitvector a into b.
 */
void bvconstant_copy(bvconstant_t *b, uint32_t n, const uint32_t *a) {
  uint32_t k;

  k = (n + 31) >> 5;
  bvconstant_set_bitsize(b, n);
  bvconst_set(b->data, k, a);
  bvconst_normalize(b->data, n);
}



/*
 * Resize and copy constant into b
 */
void bvconstant_copy64(bvconstant_t *b, uint32_t n, uint64_t a) {
  uint32_t k;

  k = (n + 31) >> 5;

  bvconstant_set_bitsize(b, n);
  bvconst_set64(b->data, k, a);
  bvconst_normalize(b->data, n);
}




/****************************************
 *  OPERATIONS ON BIT-VECTOR CONSTANTS  *
 ***************************************/

/*
 * Return 1^k where 0 <= k <= 31. This is just to avoid ((uint32_t) 1) << k
 * everywhere
 */
static inline uint32_t bitp(uint32_t k) {
  assert(k < 32);
  return ((uint32_t) 1) << k;
}

/*
 * Normalize: n = number of bits in bv
 * - let k = ceiling(n/32) and d = 32 k - n
 * - then bv is an array of k words
 * - normalization sets the d higher order bits of n to zero
 */
void bvconst_normalize(uint32_t *bv, uint32_t n) {
  uint32_t k, r;

  r = n & 0x1f;      // r = n mod 32
  if (r > 0) {
    k = n >> 5;        // k = floor(n/32)
    bv[k] &= (uint32_t) (bitp(r) - 1);
  }
}

/*
 * Check whether bv is normalized modulo 2^n (i.e., whether the high
 * order bits are 0).
 */
bool bvconst_is_normalized(const uint32_t *bv, uint32_t n) {
  uint32_t k, r;

  r = n & 0x1f;  // r = n mod 32
  k = n >> 5;    // k = floor (n/32)
  return r == 0 || (bv[k] & ~((uint32_t) (bitp(r) - 1))) == 0;
}


/*
 * Operations on single bits
 */
bool bvconst_tst_bit(const uint32_t *bv, uint32_t i) {
  uint32_t j, mask;

  j = i >> 5;
  mask = bitp(i & 0x1f);
  return bv[j] & mask; // converted to bool --> 0 or 1
}

void bvconst_set_bit(uint32_t *bv, uint32_t i) {
  uint32_t j, mask;

  j = i >> 5;
  mask = bitp(i & 0x1f);
  bv[j] |= mask;
}

void bvconst_clr_bit(uint32_t *bv, uint32_t i) {
  uint32_t j, mask;

  j = i >> 5;
  mask = bitp(i & 0x1f);
  bv[j] &= ~mask;
}

void bvconst_flip_bit(uint32_t *bv, uint32_t i) {
  uint32_t j, mask;

  j = i >> 5;
  mask = bitp(i & 0x1f);
  bv[j] ^= mask;
}

void bvconst_assign_bit_old(uint32_t *bv, uint32_t i, bool bit) {
  uint32_t j, mask;

  j = i >> 5;
  mask = bitp(i & 0x1f);
  if (bit) {
    bv[j] |= mask;
  } else {
    bv[j] &= ~mask;
  }
}

void bvconst_assign_bit(uint32_t *bv, uint32_t i, bool bit) {
  uint32_t j, mask, x;

  j = i >> 5;
  mask = bitp(i & 0x1f);
  x = ((uint32_t) bit) << (i & 0x1f);
  bv[j] ^= (bv[j] ^ x) & mask;
}





/*
 * Assignment operations: bv is the target
 * - k = number of 32-bit words in bv
 */
// set to 0b0000....000
void bvconst_clear(uint32_t *bv, uint32_t k) {
  assert(k > 0);
  do {
    *bv++ = 0;
    k --;
  } while (k > 0);
}

// set to 0b0000000...001
void bvconst_set_one(uint32_t *bv, uint32_t k) {
  assert(k > 0);
  *bv ++ = 1;
  while (k > 1) {
    *bv++ = 0;
    k --;
  }
}

// set to 0b1111....111
void bvconst_set_minus_one(uint32_t *bv, uint32_t k) {
  assert(k > 0);
  do {
    *bv ++ = 0xffffffff;
    k --;
  } while (k>0);
}

// set low-order word to a, rest to 0
void bvconst_set32(uint32_t *bv, uint32_t k, uint32_t a) {
  assert(k > 0);
  * bv++ = a;
  while (k > 1) {
    *bv++ = 0;
    k --;
  }
}

// set low-order word to a, then sign extend
void bvconst_set32_signed(uint32_t *bv, uint32_t k, int32_t a) {
  uint32_t p;

  assert(k > 0);
  * bv ++ = a;
  p = (a >= 0) ? 0 : 0xffffffff;
  while (k > 1) {
    *bv ++ = p;
    k --;
  }
}

// set two low-order words to a, rest to 0
void bvconst_set64(uint32_t *bv, uint32_t k, uint64_t a) {
  assert(k > 0);

  if (k == 1) {
    * bv= (uint32_t) (a & 0xffffffff);
  } else {
    * bv ++ = (uint32_t) (a & 0xffffffff);
    * bv ++ = (uint32_t) (a >> 32);
    while (k > 2) {
      * bv ++ = 0;
      k --;
    }
  }
}

// set the two low-order words to a, then sign extend
void bvconst_set64_signed(uint32_t *bv, uint32_t k, int64_t a) {
  uint32_t p;

  assert(k > 0);

  if (k == 1) {
    * bv = (uint32_t) (a & 0xffffffff);
  } else {
    * bv ++ = (uint32_t) (a & 0xffffffff);
    * bv ++ = (uint32_t) (a >> 32);
    p = (a >= 0) ? 0 : 0xffffffff;
    while (k > 2) {
      * bv ++ = p;
      k --;
    }
  }
}


// assign 32k low-order bits of z
void bvconst_set_mpz(uint32_t *bv, uint32_t k, const mpz_t z) {
  mpz_t aux;

  assert(mpz_sgn(z) >= 0); // z must be  non-negative
  assert(k > 0);

  if (k == 1) {
    *bv = (uint32_t) mpz_get_ui(z);
  } else {
    mpz_init_set(aux, z);   // aux := copy of z

    do {
      *bv++ = (uint32_t) mpz_get_ui(aux);
      mpz_fdiv_q_2exp(aux, aux, 32);
      k --;
    } while (k > 0);

    mpz_clear(aux);
  }
}

// conversion from bv to mpz_t
void bvconst_get_mpz(const uint32_t *bv, uint32_t k, mpz_t z) {
  assert(k > 0);

  k --;
  mpz_set_ui(z, bv[k]);
  while (k > 0) {
    k --;
    mpz_mul_2exp(z, z, 32);
    mpz_add_ui(z, z, bv[k]);
  }
}

// assign bv from r. r must be a positive integer.
void bvconst_set_q(uint32_t *bv, uint32_t k, rational_t *r) {
  assert(q_is_integer(r));

  if (is_rat32(r)) {
    bvconst_set32(bv, k, get_num(r));
  } else {
    bvconst_set_mpz(bv, k, mpq_numref(get_gmp(r)));
  }
}

// copy a into b: b has k words. a has k or more words
void bvconst_set(uint32_t *bv, uint32_t k, const uint32_t *a) {
  assert(k > 0);
  do {
    *bv ++  = *a++;
    k --;
  } while (k > 0);
}



/*
 * Other constant assignments: n = number of bits
 * - set_min_signed:  bv := 0b100...000
 * - set_max_signed:  bv := 0b011...111
 * - bv must be large enough (at least ceil(n/32) words)
 * - n must be positive
 * - bv is normalized
 */
void bvconst_set_min_signed(uint32_t *bv, uint32_t n) {
  assert(n > 0);
  bvconst_clear(bv, (n + 31) >> 5);
  bvconst_set_bit(bv, n-1);
}

void bvconst_set_max_signed(uint32_t *bv, uint32_t n) {
  assert(n > 0);
  bvconst_set_minus_one(bv, (n + 31) >> 5);
  bvconst_clr_bit(bv, n-1);
  bvconst_normalize(bv, n);
}


/*
 * Assign a to bv, padding with 0
 * - bv has m = 32k bits
 * - a has n = 32d + r bits with d < k and 0 <= r <= 31
 */
static void bvconst_set_p0(uint32_t *bv, uint32_t k, const uint32_t *a, uint32_t d, uint32_t r) {
  assert(r <= 31);
  assert(d < k);

  while (d > 0) {
    *bv ++ = * a++;
    d --;
    k --;
  }
  if (r > 0) {
    *bv ++ = (*a) & ((1<<r) - 1);
    k --;
  }
  while (k > 0) {
    *bv ++ = 0;
    k --;
  }
}

// padding with 1
static void bvconst_set_p1(uint32_t *bv, uint32_t k, const uint32_t *a, uint32_t d, uint32_t r) {
  uint32_t mask;

  assert(r <= 31);
  assert(d < k);

  while (d > 0) {
    *bv ++ = * a++;
    d --;
    k --;
  }
  if (r > 0) {
    mask = bitp(r) - 1;
    *bv ++ = (~mask) | ((*a) & mask);
    k --;
  }
  while (k > 0) {
    *bv ++ = 0xffffffff;
    k --;
  }
}

/*
 * b: n-bit value, a: m-bit value with m <= n
 * - assign a to b with padding defined by mode:
 * - mode = 0: padding with 0
 * - mode = 1: padding with 1
 * - mode = -1: sign extension
 */
void bvconst_set_extend(uint32_t *bv, uint32_t n, const uint32_t *a, uint32_t m, int32_t mode) {
  uint32_t k, d, r;

  assert(0 < m && m <= n);
  assert(mode == 0 || mode == 1 || mode == -1);

  k = (n + 31) >> 5;

  if (n == m) {
    bvconst_set(bv, k, a);
    return;
  }

  d = m >> 5;
  r = m & 0x1f;

  if (mode < 0) {
    mode = bvconst_tst_bit(a, m-1);
  }

  if (mode) {
    bvconst_set_p1(bv, k, a, d, r);
  } else {
    bvconst_set_p0(bv, k, a, d, r);
  }
}


/*
 * Assignment from array a of n elements
 * - bit i of bv = 0 iff a[i] = 0
 */
void bvconst_set_array(uint32_t *bv, const int32_t *a, uint32_t n) {
  uint32_t i;
  assert(n > 0);

  // suboptimal but should be enough
  for (i=0; i<n; i++) bvconst_assign_bit(bv, i, a[i]);
}



/*
 * Reverse operation: store bit i of bv in a[i].
 */
void bvconst_get_array(const uint32_t *bv, int32_t *a, uint32_t n) {
  uint32_t i;
  assert(n > 0);

  for (i=0; i<n; i++) a[i] = bvconst_tst_bit(bv, i);
}


/*
 * Print bv constant of size n
 */
void bvconst_print(FILE *f, const uint32_t *bv, uint32_t n) {
  assert(n>0);

  fprintf(f, "0b");
  do {
    n --;
    fprintf(f, "%u", (unsigned) bvconst_tst_bit(bv, n));
  } while (n > 0);
}



/*
 * Convert a string of '0' and '1's to a bitvector constant.
 * - n = number of bits
 * - s must be at least n character long
 *
 * Reads the n first characters of s. All must be '0' or '1'
 * - the string is assumed in big-endian format: the
 *   first character is the high-order bit.
 *
 * Return code: -1 if the string format is wrong, 0 otherwise.
 */
int32_t bvconst_set_from_string(uint32_t *bv, uint32_t n, const char *s) {
  char c;

  assert(n > 0);

  do {
    n --;
    c = *s;
    s ++;
    if (c == '0') {
      bvconst_clr_bit(bv, n);
    } else if (c == '1') {
      bvconst_set_bit(bv, n);
    } else {
      return -1;
    }
  } while (n > 0);

  return 0;
}


/*
 * Convert a string, interpreted as hexadecimal digits to a bitvector constant.
 * - n = number of characters, must be positive.
 * - s must be at least n character long
 *
 * Reads the n first characters of s.
 * All must be '0' to '9' or 'a' to 'f' or 'A' to 'F'
 * - the string is assumed in big-endian format: the
 *   first character defines the high-order 4 bits.
 *
 * Return code: -1 if the string format is wrong, 0 otherwise.
 */
static uint32_t hextoint(char c) {
  if ('0' <= c && c <= '9') {
    return c - '0';
  } else if ('a' <= c && c <= 'f') {
    return 10 + (c - 'a');
  } else {
    assert('A' <= c && c <= 'F');
    return 10 + (c - 'A');
  }
}

int32_t bvconst_set_from_hexa_string(uint32_t *bv, uint32_t n, const char *s) {
  char c;
  uint32_t hex;

  assert(n > 0);

  n <<= 2; // n * 4
  do {
    c = *s;
    s ++;
    if (isxdigit((int) c)) {
      hex = hextoint(c);
      // set bits n-1 to n-4
      // suboptimal but that should do for now
      n --;
      bvconst_assign_bit(bv, n, hex & 8);
      n --;
      bvconst_assign_bit(bv, n, hex & 4);
      n --;
      bvconst_assign_bit(bv, n, hex & 2);
      n --;
      bvconst_assign_bit(bv, n, hex & 1);
    } else {
      return -1;
    }
  } while (n > 0);

  return 0;
}



/*
 * Population count: number of 1 bits in bv
 * - bv must be normalized
 * - k must be the size of bv in words
 */
uint32_t bvconst_popcount(const uint32_t *bv, uint32_t k) {
  uint32_t i, c;

  c = 0;
  for (i=0; i<k; i++) {
    c += popcount32(bv[i]);
  }
  return c;
}




/*
 * Bitwise operations: all modify the first argument bv
 * - bv and a are both assumed to have k words
 */
void bvconst_complement(uint32_t *bv, uint32_t k) {
  assert(k > 0);
  do {
    *bv = ~ (*bv);
    bv ++;
    k --;
  } while (k > 0);
}

void bvconst_and(uint32_t *bv, uint32_t k, uint32_t *a) {
  assert(k > 0);
  do {
    *bv ++ &= *a ++;
    k --;
  } while (k > 0);
}

void bvconst_or(uint32_t *bv, uint32_t k, uint32_t *a) {
  assert(k > 0);
  do {
    *bv ++ |= *a ++;
    k --;
  } while (k > 0);
}

void bvconst_xor(uint32_t *bv, uint32_t k, uint32_t *a) {
  assert(k > 0);
  do {
    *bv ++ ^= *a ++;
    k --;
  } while (k > 0);
}



/*
 * - shift bv to the left by 32d + r, padding with 0
 * - k = size of bv in words: bv has 32k bits
 * - 0 <= r <= 31 and  0 <= d <= k-1
 */
static void bvconst_shift_left0(uint32_t *bv, uint32_t k, uint32_t d, uint32_t r) {
  uint32_t i, j, s;
  uint64_t aux;

  assert(r <= 31);
  assert(d < k);

  s = 32 - r;
  j = k - 1;
  i = j - d;
  aux = (uint64_t) bv[i];
  while (i > 0) {
    i --;
    aux <<= 32;
    aux |= bv[i];
    bv[j] = (uint32_t) (aux >> s);
    j --;
  }
  bv[j] = (uint32_t) (aux << r);
  while (j > 0) {
    j --;
    bv[j] = 0;
  }
}


/*
 * - shift bv to the left by 32d + r, padding with 1
 * - k = size of bv in words: bv has 32k bits
 * - 0 <= r <= 31 and  0 <= d <= k-1
 */
static void bvconst_shift_left1(uint32_t *bv, uint32_t k, uint32_t d, uint32_t r) {
  uint32_t i, j;
  uint64_t aux;

  assert(r <= 31);
  assert(d < k);

  r = 32 - r;
  j = k - 1;
  i = j - d;
  aux = (uint64_t) bv[i];
  while (i > 0) {
    i --;
    aux <<= 32;
    aux |= bv[i];
    bv[j] = (uint32_t) (aux >> r);
    j --;
  }
  aux <<= 32;
  aux |= 0xffffffff;
  bv[j] = (uint32_t) (aux >> r);
  while (j > 0) {
    j --;
    bv[j] = 0xffffffff;
  }
}


/*
 * Shift by m bits to the left, padding with b
 * - n = size of bv in bits
 * - m must be between 0 and n
 * - b = false ==> padding with 0, otherwise padding with 1
 */
void bvconst_shift_left(uint32_t *bv, uint32_t n, uint32_t m, bool b) {
  uint32_t k, d, r;
  assert(0 < n && m <= n);

  if (m == 0) return;

  // special case: n == m
  k = (n + 31) >> 5;  // bv contains k 32-bit words
  if (m == n) {
    if (b) {
      bvconst_set_minus_one(bv, k);
    } else {
      bvconst_clear(bv, k);
    }
    return;
  }

  d = m >> 5;
  r = m & 0x1f;
  if (b) {
    bvconst_shift_left1(bv, k, d, r);
  } else {
    bvconst_shift_left0(bv, k, d, r);
  }
}



/*
 * - shift bv to the right by 32d + r, padding with 0
 * - k = size of bv in words: bv has 32k bits
 * - 0 <= r <= 31 and  0 <= d <= k-1
 */
static void bvconst_shift_right0(uint32_t *bv, uint32_t k, uint32_t d, uint32_t r) {
  uint32_t i, j;
  uint64_t aux;

  assert(r <= 31);
  assert(d < k);

  j = 0;
  i = d;
  aux = (uint64_t) bv[i];
  while (i < k-1) {
    i ++;
    aux |= ((uint64_t) bv[i]) << 32;
    bv[j] = (uint32_t) (aux >> r);
    aux >>= 32;
    j ++;
  }
  bv[j] = (uint32_t) (aux >> r);
  while (j < k-1) {
    j ++;
    bv[j] = 0;
  }
}

/*
 * - shift bv to the right by 32d + r, padding with 1
 * - k = size of bv in words: bv has 32k bits
 * - 0 <= r <= 31 and  0 <= d <= k-1
 */
static void bvconst_shift_right1(uint32_t *bv, uint32_t k, uint32_t d, uint32_t r) {
  uint32_t i, j;
  uint64_t aux;

  assert(r <= 31);
  assert(d < k);

  j = 0;
  i = d;
  aux = (uint64_t) bv[i];
  while (i < k-1) {
    i ++;
    aux |= ((uint64_t) bv[i]) << 32;
    bv[j] = (uint32_t) (aux >> r);
    aux >>= 32;
    j ++;
  }
  aux |= ((uint64_t) 0xffffffff) << 32;
  bv[j] = (uint32_t) (aux >> r);
  while (j < k-1) {
    j ++;
    bv[j] = 0xffffffff;
  }
}


/*
 * Shift by m bits to the right, padding with b
 * - n = size of bv in bits
 * - m must be between 0 and n
 * - b = false ==> padding with 0, otherwise padding with 1
 */
void bvconst_shift_right(uint32_t *bv, uint32_t n, uint32_t m, bool b) {
  uint32_t k, d, r, s;
  assert(0 < n && m <= n);

  if (m == 0) return;

  // special case: n == m
  k = (n + 31) >> 5;  // bv contains k 32-bit words
  if (m == n) {
    if (b) {
      bvconst_set_minus_one(bv, k);
    } else {
      bvconst_clear(bv, k);
    }
    return;
  }

  d = m >> 5;
  r = m & 0x1f;
  s = n & 0x1f;
  if (b) {
    if (s > 0) {
      // bvconst_shift_right requires bv to be 32k words
      // we force the (32-s) high order bits of bv[k-1] to 1
      bv[k-1] |= (((uint32_t) 0xffffffff) << s);
    }
    bvconst_shift_right1(bv, k, d, r);
  } else {
    if (s > 0) {
      // force the high-order bits to 0
      bv[k-1] &= ~(((uint32_t) 0xffffffff) << s);
    }
    bvconst_shift_right0(bv, k, d, r);
  }
}


/*
 * Convert constant c into a shift amount between 0 and n
 * - n = number of bits of c
 * - if c's value is more than n, return n.
 *   otherwise return c's value
 */
static uint32_t bvshift_amount(uint32_t *c, uint32_t n) {
  uint32_t k, i, s;

  assert(n > 0);

  k = (n + 31) >> 5;     // number of words in c
  s = bvconst_get32(c);  // s = lower order word of c

  // check that the high order words are zero
  for (i=1; i<k; i++) {
    if (c[i] != 0) return n;
  }

  return (s < n) ? s : n;
}


/*
 * Logical shift left: (a << b)
 * - store the result in *bv and normalize
 * - n = number of bits in a and b
 */
void bvconst_lshl(uint32_t *bv, uint32_t *a, uint32_t *b, uint32_t n) {
  uint32_t k, s;

  s = bvshift_amount(b, n);
  assert(0 <= s && s <= n);
  k = (n + 31) >> 5;
  bvconst_set(bv, k, a);
  bvconst_shift_left(bv, n, s, false);
  bvconst_normalize(bv, n);
}

// in-place variant: bv := bv << b
void bvconst_lshl_inplace(uint32_t *bv, uint32_t *b, uint32_t n) {
  uint32_t s;

  s = bvshift_amount(b, n);
  assert(0 <= s && s <= n);
  bvconst_shift_left(bv, n, s, false);
  bvconst_normalize(bv, n);
}


/*
 * Logical shift right: (a >> b)
 * - store the result in *bv and normalize
 * - n = number of bits in a and b
 */
void bvconst_lshr(uint32_t *bv, uint32_t *a, uint32_t *b, uint32_t n) {
  uint32_t k, s;

  s = bvshift_amount(b, n);
  assert(0 <= s && s <= n);
  k = (n + 31) >> 5;
  bvconst_set(bv, k, a);
  bvconst_shift_right(bv, n, s, false);
  bvconst_normalize(bv, n);
}

// in-place variant: bv := bv >> b
void bvconst_lshr_inplace(uint32_t *bv, uint32_t *b, uint32_t n) {
  uint32_t s;

  s = bvshift_amount(b, n);
  assert(0 <= s && s <= n);
  bvconst_shift_right(bv, n, s, false);
  bvconst_normalize(bv, n);
}

/*
 * Arithmetic shift right: (a >> b)
 * - store the result in *bv and normalize
 * - n = number of bits in a and b
 */
void bvconst_ashr(uint32_t *bv, uint32_t *a, uint32_t *b, uint32_t n) {
  uint32_t k, s;
  bool sign;

  s = bvshift_amount(b, n);
  assert(0 <= s && s <= n);
  k = (n + 31) >> 5;
  bvconst_set(bv, k, a);
  sign = bvconst_tst_bit(a, n-1);
  bvconst_shift_right(bv, n, s, sign);
  bvconst_normalize(bv, n);
}

// in-place variant: bv := bv >> b
void bvconst_ashr_inplace(uint32_t *bv, uint32_t *b, uint32_t n) {
  uint32_t s;
  bool sign;

  s = bvshift_amount(b, n);
  assert(0 <= s && s <= n);
  sign = bvconst_tst_bit(bv, n-1);
  bvconst_shift_right(bv, n, s, sign);
  bvconst_normalize(bv, n);
}


/*
 * Extract subvector a[l..(h-1)] and store it in bv
 * - bv must have size k = ceil((h - l) / 32)
 */
void bvconst_extract(uint32_t *bv, uint32_t *a, uint32_t l, uint32_t h) {
  uint32_t r, i, to_move;
  uint64_t aux;

  assert(l < h);

  i = l >> 5;       // first word to read
  r = l & 0x1f;     // shift
  to_move = h - l;  // number of bits to move

  aux = (uint64_t) a[i];
  while (to_move > 32) {
    i ++;
    aux |= ((uint64_t) a[i]) << 32;
    *bv = (uint32_t)(aux >> r);
    bv ++;
    aux >>= 32;
    to_move -= 32;
  }

  assert(to_move > 0);
  if (r > 0) {
    aux |= ((uint64_t) a[i+1]) << 32;
  }
  *bv = (uint32_t)(aux >> r);
}


/*
 * Concat(a, b): (a | (b << n))
 * - a has n bits
 * - b has m bits
 * - result is stored in bv
 * - bv must be large enough for n + m bits.
 * - low-order bits = a
 * - high-order bits = b
 */
void bvconst_concat(uint32_t *bv, uint32_t *a, uint32_t n, uint32_t *b, uint32_t m) {
  uint32_t r, s, t, i, x, y;

  //  assert(n > 0);
  //  assert(m > 0);

  i = n >> 5;
  r = n & 0x1f;
  while (i > 0) {
    *bv ++ = *a ++;
    i --;
  }

  if (r == 0) {
    i = (m + 31) >> 5;
    do {
      * bv ++ = *b ++;
      i --;
    } while (i > 0);

  } else {
    x = (*a) & (bitp(r) - 1);
    t = 32 - r;
    i = m >> 5;
    while (i > 0) {
      y = *b++;
      *bv ++ = (y << r) | x;
      x = y >> t;
      i --;
    }
    s = m & 0x1f;
    if (s == 0) {
      *bv = x;
    } else {
      y = *b;
      *bv ++ = (y << r) | x;
      if (s > t) {
        *bv = y >> t;
      }
    }
  }
}


/*
 * Arithmetic operations
 */
// bv := - bv
void bvconst_negate(uint32_t *bv, uint32_t k) {
  int64_t aux;

  assert (k > 0);
  aux = 0;
  do {
    aux -= *bv;
    *bv = (uint32_t) aux;
    aux >>= 32;
    bv ++;
    k --;
  } while (k > 0);
}

// bv := - a
void bvconst_negate2(uint32_t *bv, uint32_t k, uint32_t *a) {
  int64_t aux;

  assert (k > 0);
  aux = 0;
  do {
    aux -= *a;
    *bv = (uint32_t) aux;
    aux >>= 32;
    bv ++;
    a ++;
    k --;
  } while (k > 0);
}

// bv := bv + a
void bvconst_add(uint32_t *bv, uint32_t k, uint32_t *a) {
  uint64_t aux;

  assert(k>0);
  aux = 0;
  do {
    aux += ((uint64_t) (*bv)) + ((uint64_t) (*a));
    *bv = (uint32_t) aux;
    aux >>= 32;
    a ++;
    bv ++;
    k --;
  } while (k > 0);
}

// bv := bv + 1
void bvconst_add_one(uint32_t *bv, uint32_t k) {
  uint64_t aux;

  assert(k>0);
  aux = 1;
  do {
    aux += (uint64_t) (*bv);
    *bv = (uint32_t) aux;
    aux >>= 32;
    bv ++;
    k --;
  } while (k > 0);
}

// bv := a1 + a2
void bvconst_add2(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2) {
  uint64_t aux;

  assert(k>0);
  aux = 0;
  do {
    aux += ((uint64_t) (*a1)) + ((uint64_t) (*a2));
    *bv = (uint32_t) aux;
    aux >>= 32;
    a1 ++;
    a2 ++;
    bv ++;
    k --;
  } while (k > 0);
}


// bv := bv - a
void bvconst_sub(uint32_t *bv, uint32_t k, uint32_t *a) {
  int64_t aux;

  assert(k > 0);
  aux = 0;
  do {
    aux += ((uint64_t) (*bv)) - ((uint64_t) (*a));
    *bv = (uint32_t) aux;
    aux >>= 32;
    a ++;
    bv ++;
    k --;
  } while (k > 0);
}

// bv := bv - 1
void bvconst_sub_one(uint32_t *bv, uint32_t k) {
  int64_t aux;

  assert(k > 0);
  aux = -1;
  do {
    aux += (uint64_t) (*bv);
    *bv = (uint32_t) aux;
    aux >>= 32;
    bv ++;
    k --;
  } while (k > 0);
}

// bv := a1 - a2
void bvconst_sub2(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2) {
  int64_t aux;

  assert(k > 0);
  aux = 0;
  do {
    aux += ((uint64_t) (*a1)) - ((uint64_t) (*a2));
    * bv = (uint32_t) aux;
    aux >>= 32;
    a1 ++;
    a2 ++;
    bv ++;
    k --;
  } while (k > 0);
}


// bv := bv + a1 * a2
void bvconst_addmul(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2) {
  uint64_t aux, f;
  uint32_t j;

  assert (k > 0);
  do {
    f = ((uint64_t) (*a1));
    aux = 0;
    for (j=0; j<k; j++) {
      aux += bv[j] + f * a2[j];
      bv[j] = (uint32_t) aux;
      aux >>= 32;
    }
    bv ++;
    a1 ++;
    k --;
  } while (k > 0);
}

// bv := bv - a1 * a2
void bvconst_submul(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2) {
  assert (k > 0);

  /*
   * We can't adapt addmul in a simple way
   * since bv[i] - f * a2[j] may not fit in a signed 64bit integer
   * So we compute:
   *   bv_1 = (2^32k - 1) - bv = bitwise complement of bv
   *   bv_2 = (bv_1 + a1 * a2) mod (2^32k)
   *   bv_3 = (2^32k - 1) - bv_2 = bitwise complement of bv_2
   * then
   *   bv_2 = (a1 * a2 - bv - 1) mod (2^32k)
   *   bv_3 = (bv - a1 * a1) mod (2^32k) = what we want
   */
  bvconst_complement(bv, k);
  bvconst_addmul(bv, k, a1, a2);
  bvconst_complement(bv, k);
}

// bv := a1 * a2
void bvconst_mul2(uint32_t *bv, uint32_t k, uint32_t *a1, uint32_t *a2) {
  bvconst_clear(bv, k);
  bvconst_addmul(bv, k, a1, a2);
}

// bv := bv * a
void bvconst_mul(uint32_t *bv, uint32_t k, uint32_t *a) {
  uint32_t tmp[k]; // Warning: this is a GCC extension of C. Dangerous is k is large

  bvconst_set(tmp, k, bv);
  bvconst_clear(bv, k);
  bvconst_addmul(bv, k, tmp, a);
}


/*
 * Multiplication by a power
 * - compute bv * a ^ d and store the result in bv
 * - bv and a must be distinct and have word size = k
 */
void bvconst_mulpower(uint32_t *bv, uint32_t k, uint32_t *a, uint32_t d) {
  uint32_t tmp[k];
  uint32_t sq[k];

  // deal with small exponents d
  if (d == 0) return; // we take 0^0 = 1

  if (d == 1) {
    bvconst_mul(bv, k, a);
    return;
  }

  if (d == 2) {
    bvconst_mul2(tmp, k, a, a);
    bvconst_mul(bv, k, tmp);
    return;
  }

  // general case: d>=3
  bvconst_set(tmp, k, a);
  for (;;) {
    assert(d > 0);
    if ((d & 1) != 0) {
      bvconst_mul(bv, k, tmp);
    }
    d >>= 1;
    if (d == 0) return;
    bvconst_mul2(sq, k, tmp, tmp);
    bvconst_set(tmp, k, sq);
  }
}



/*
 * COMPARISONS
 */

/*
 * Tests and comparisons.
 * - k = word size
 * - bv must be normalized
 */
bool bvconst_is_zero(const uint32_t *bv, uint32_t k) {
  assert(k > 0);
  do {
    if (*bv != 0) return false;
    bv ++;
    k --;
  } while (k > 0);

  return true;
}

bool bvconst_is_one(const uint32_t *bv, uint32_t k) {
  assert(k > 0);

  if (*bv != 1) return false;
  bv ++;
  k --;

  while (k > 0) {
    if (*bv != 0) return false;
    bv++;
    k--;
  }

  return true;
}


/*
 * Check whether bv is equal to -1 (i.e., 0b11...1)
 * - n = number of bits in bv
 * - bv must be normalized
 */
bool bvconst_is_minus_one(const uint32_t *bv, uint32_t n) {
  uint32_t k, r;

  assert(n > 0);
  k = n >> 5; // n mod 32
  r = n & 31; // n rem 32
  assert(n == 32 * k + r && r < 32);

  while (k > 0) {
    if (*bv != ~((uint32_t) 0)) {
      return false;
    }
    bv ++;
    k --;
  }

  return r == 0 || *bv == (~((uint32_t) 0)) >> (32 - r);
}


/*
 * Check whether bv is 0b100..0 (smallest negative signed integer)
 * - n = number of bits in bv
 * - bv must be normalized.
 */
bool bvconst_is_min_signed(const uint32_t *bv, uint32_t n) {
  uint32_t k, r;

  assert(n > 0);
  k = (n + 31) >> 5;  // number of 32bit words
  r = n & 31;         // n rem 31
  if (r == 0) {
    r = 32;
  }

  // all low-order words must be 0
  while (k > 1) {
    if (*bv != 0) {
      return false;
    }
    bv ++;
    k --;
  }

  // the high-order word must be 0b10000000 >> (32 - r)
  assert(0 <= 32 - r && 32 - r <= 31);
  return *bv == ((uint32_t) INT32_MIN) >> (32 - r);
}


/*
 * Check whether bv is 0b0111..1 (largest positive signed integer)
 * - n = number of bits in bv
 * - bv must be normalized
 */
bool bvconst_is_max_signed(const uint32_t *bv, uint32_t n) {
  uint32_t k, r;

  assert(n > 0);
  k = (n + 31) >> 5;  // number of 32bit words
  r = n & 31;         // n rem 31
  if (r == 0) {
    r = 32;
  }

  // all low-order words must be 0xFFFF
  while (k > 1) {
    if (*bv != ~((uint32_t) 0)) {
      return false;
    }
    bv ++;
    k --;
  }

  // the high-order word must be 0b011111111 >> (32 - r)
  assert(0 <= 32 - r && 32 - r <= 31);
  return *bv == ((uint32_t) INT32_MAX) >> (32 - r);
}




/*
 * Check whether bv is a power of 2 and if so return n such
 * that bv = 2^n. Otherwise, return -1.
 * - bv must be normalized
 * - k = number of words in bv
 */
int32_t bvconst_is_power_of_two(const uint32_t *bv, uint32_t k) {
  uint32_t u;
  int32_t n, p;

  assert(k > 0);
  n = 0;

  // skip low-order words that are zero
  while (*bv == 0) {
    bv ++;
    n += 32;
    k --;

    if (k == 0) return -1; // 0 not a power of 2
  }

  u = *bv;
  assert(k > 0 && u > 0);

  p = ctz(u);   // p = index of the rightmost 1 in u
  assert(0 <= p && p <= 31);
  if (u != (1<<p)) {
    // u is not equal to 2^p so bv is not a power of 2
    return -1;
  }

  // check whether the remaining words of bv are all zero
  bv ++;
  k --;
  while (k > 0) {
    if (*bv != 0) return -1;
    bv ++;
    k --;
  }

  return n + p;
}

/*
 * Number of trailing zeros, k = number of words in bv, bv must be normalized
 * - return the index of the lowest-order bit of bv that's not 0
 * - returns -1 if bv is zero
 */
int32_t bvconst_ctz(const uint32_t *bv, uint32_t k) {
  uint32_t u;
  int32_t n, p;

  assert(k > 0);
  n = 0;

  // skip low-order words that are zero
  while (*bv == 0) {
    bv ++;
    n += 32;
    k --;
    if (k == 0) return -1; // 0 gives -1
  }

  u = *bv;
  assert(k > 0 && u > 0);

  p = ctz(u);   // p = index of the rightmost 1 in u
  return n + p;
}



/*
 * Check whether a and b are equal, both must be of size k.
 *
 * Both a and b must be normalized (modulo 2^n) if n = bitsize
 * of a and b, and n != 32 k
 */
bool bvconst_eq(const uint32_t *a, const uint32_t *b, uint32_t k) {
  assert(k > 0);
  do {
    if (*a != *b) return false;
    a ++;
    b ++;
    k --;
  } while (k > 0);

  return true;
}


/*
 * Check whether a <= b (interpreted as unsigned numbers)
 * - both a and b must be of bitsize n (with n>0) and normalized
 */
bool bvconst_le(const uint32_t *a, const uint32_t *b, uint32_t n) {
  uint32_t k;

  assert(n > 0);
  n --;
  k = n >> 5; // k = n/52
  while (k > 0 && a[k] == b[k]) k--;

  return a[k] <= b[k];
}


/*
 * Check whether a <= b (interpreted as signed numbers)
 * - both a and b must be of bitsize n (with n>0) and normalized
 */
bool bvconst_sle(const uint32_t *a, const uint32_t *b, uint32_t n) {
  uint32_t k, mask, sign_a, sign_b;

  assert(n > 0);

  n --;
  k = n >> 5;
  mask = bitp(n & 0x1f);

  sign_a = a[k] & mask;
  sign_b = b[k] & mask;

  if (sign_a == sign_b) {
    while (k > 0 && a[k] == b[k]) k--;
    return a[k] <= b[k];
  } else {
    return sign_a > sign_b; //i.e. sign(a) = 1 and sign(b) = 0
  }
}






/*
 * Compute hash of constant a. n = bitsize
 * - a must be normalized for this to be compatible with eq
 */
uint32_t bvconst_hash(const uint32_t *a, uint32_t n) {
  uint32_t k;

  assert(bvconst_is_normalized(a, n));

  k = (n + 31) >> 5;
  return jenkins_hash_array(a, k, 0x741a8d7a + n);
}




/*
 * DIVISIONS
 */

/*
 * Initialize z and copy a into z
 * - a is interpreted as an unsigned n-bit integer
 * - a must be normalized modulo (2^n)
 */
static inline void unsigned_bv2mpz(mpz_t z, uint32_t n, const uint32_t *a) {
  uint32_t k;

  k = (n + 31) >> 5;
  mpz_init2(z, n);
  bvconst_get_mpz(a, k, z);
}

/*
 * Initialize z and copy a into z
 * - a is interpreted as a signed n-bit integer
 * - a must be normalized modulo (2^n)
 */
static void signed_bv2mpz(mpz_t z, uint32_t n, const uint32_t *a) {
  mpz_t aux;
  uint32_t k;

  assert(n > 0);

  k = (n + 31) >> 5;
  mpz_init2(z, n);
  bvconst_get_mpz(a, k, z);
  if (bvconst_tst_bit(a, n-1)) { // sign bit = 1
    mpz_init_set_si(aux, -1);
    mpz_mul_2exp(aux, aux, n);
    mpz_add(z, z, aux);
    mpz_clear(aux);
  }
}

/*
 * Copy z into a (like set_mpz but don't use an auxiliary mpz)
 * - n = number of bits
 * FIX THIS: THE SIGN OF Z IS IGNORED
 */
static void mpz2bv(uint32_t *a, uint32_t n, mpz_t z) {
  mpz_t aux;
  uint32_t k;

  if (mpz_sgn(z) < 0) {
    // add 2^n to z
    mpz_init_set_ui(aux, 1);
    mpz_mul_2exp(aux, aux, n);
    mpz_add(z, z, aux);
    mpz_clear(aux);
  }

  k = (n + 31) >> 5;
  do {
    *a++ = (uint32_t) mpz_get_ui(z);
    mpz_fdiv_q_2exp(z, z, 32);
    k --;
  } while (k > 0);
}


/*
 * Division and remainder
 * - a1 and a2 must be normalized
 * - n = number of bits in a1 and a2 (also in bv)
 * - a2 must be nonzero
 * - udiv2: bv := a1/a2
 */
// unsigned division
void bvconst_udiv2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  mpz_t z1, z2;

  assert(n > 0);
  if (n <= 32) {
    *bv = (*a1) / (*a2);
  } else {
    unsigned_bv2mpz(z1, n, a1);
    unsigned_bv2mpz(z2, n, a2);
    mpz_fdiv_q(z1, z1, z2); // z1 := z1/z2
    mpz2bv(bv, n, z1);
    mpz_clear(z1);
    mpz_clear(z2);
  }
}

// unsigned remainder
void bvconst_urem2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  mpz_t z1, z2;

  assert(n > 0);
  if (n <= 32) {
    *bv = (*a1) % (*a2);
  } else {
    unsigned_bv2mpz(z1, n, a1);
    unsigned_bv2mpz(z2, n, a2);
    mpz_fdiv_r(z1, z1, z2); // z1 := z1 mod z2
    mpz2bv(bv, n, z1);
    mpz_clear(z1);
    mpz_clear(z2);
  }
}

// signed division
void bvconst_sdiv2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  mpz_t z1, z2;

  signed_bv2mpz(z1, n, a1);
  signed_bv2mpz(z2, n, a2);
  mpz_tdiv_q(z1, z1, z2); // z1 := z1 div z2, rounding towards 0
  mpz2bv(bv, n, z1);
  mpz_clear(z1);
  mpz_clear(z2);
}

// signed rem
void bvconst_srem2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  mpz_t z1, z2;

  signed_bv2mpz(z1, n, a1);
  signed_bv2mpz(z2, n, a2);
  mpz_tdiv_r(z1, z1, z2); // z1 := remainder of z1 div z2, rounding towards 0
  mpz2bv(bv, n, z1);
  mpz_clear(z1);
  mpz_clear(z2);
}

// signed division
void bvconst_smod2(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  mpz_t z1, z2;

  signed_bv2mpz(z1, n, a1);
  signed_bv2mpz(z2, n, a2);
  mpz_fdiv_r(z1, z1, z2); // z1 := remainder of z1 div z2, rounding towards - infinity
  mpz2bv(bv, n, z1);
  mpz_clear(z1);
  mpz_clear(z2);
}


/*
 * Variants: give a default value if the divisor (a2) is zero
 */
void bvconst_udiv2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  uint32_t k;

  k = (n + 31) >> 5;
  if (bvconst_is_zero(a2, k)) {
    bvconst_set_minus_one(bv, k);
  } else {
    bvconst_udiv2(bv, n, a1,  a2);
  }
}

void bvconst_urem2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  uint32_t k;

  k = (n + 31) >> 5;
  if (bvconst_is_zero(a2, k)) {
    bvconst_set(bv, k, a1);
  } else {
    bvconst_urem2(bv, n, a1,  a2);
  }
}

void bvconst_sdiv2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  uint32_t k;

  k = (n + 31) >> 5;
  if (bvconst_is_zero(a2, k)) {
    if (bvconst_tst_bit(a1, n-1)) {
      // a1 is negative: quotient = 0b0000...01
      bvconst_set_one(bv, k);
    } else {
      // quotient = 0b1111..1
      bvconst_set_minus_one(bv, k);
    }
  } else {
    bvconst_sdiv2(bv, n, a1, a2);
  }
}

void bvconst_srem2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  uint32_t k;

  k = (n + 31) >> 5;
  if (bvconst_is_zero(a2, k)) {
    bvconst_set(bv, k, a1);
  } else {
    bvconst_srem2(bv, n, a1, a2);
  }
}

void bvconst_smod2z(uint32_t *bv, uint32_t n, uint32_t *a1, uint32_t *a2) {
  uint32_t k;

  k = (n + 31) >> 5;
  if (bvconst_is_zero(a2, k)) {
    bvconst_set(bv, k, a1);
  } else {
    bvconst_smod2(bv, n, a1, a2);
  }
}

