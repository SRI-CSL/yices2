/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SETS OF INTEGERS IN A FINITE RANGE [0 ... dsize - 1]
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/bit_tricks.h"
#include "utils/csets.h"



/*
 * BITVECTOR AS ARRAYS OF 32BIT WORDS
 */

/*
 * Allocation: n = number of bits
 */
static inline uint32_t *alloc_word_array(uint32_t n) {
  uint32_t w;

  w = (n + 31) >> 5; // ceil(n/32)
  return safe_malloc(w * sizeof(uint32_t));
}


/*
 * Set all words to 0
 */
static void clear_word_array(uint32_t *b, uint32_t n) {
  uint32_t i, w;

  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    b[i] = 0;
  }
}


/*
 * Set all bits to 1
 */
static void set_word_array(uint32_t *b, uint32_t n) {
  uint32_t i, w, r;

  w = n>>5;      // floor(n/32)
  r = n & 0x1f;  // remainder
  for (i=0; i<w; i++) {
    b[i] = 0xffffffff;
  }
  if (r > 0) {
    assert(r < 32);
    b[w] = ((uint32_t) 0xffffffff) >> (32 - r);
  }
}


/*
 * Compute the 32bit hash of b
 */
static uint32_t hash_word_array(uint32_t *b, uint32_t n) {
  uint32_t i, w, h;

  h = 0;
  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    h |= b[i];
  }
  return h;
}


/*
 * Number of 1 bits in b
 */
static uint32_t word_array_popcount(uint32_t *b, uint32_t n) {
  uint32_t i, w, c;

  c = 0;
  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    c += popcount32(b[i]);
  }

  return c;
}



/*
 * Clear/set/test bit i
 */
static void word_array_clr_bit(uint32_t *b, uint32_t i) {
  uint32_t k, r;

  k = i >> 5;
  r = i & 0x1f;
  b[k] &= ~(((uint32_t) 1) << r);
}

static void word_array_set_bit(uint32_t *b, uint32_t i) {
  uint32_t k, r;

  k = i >> 5;
  r = i & 0x1f;
  b[k] |= ((uint32_t) 1) << r;
}

static bool word_array_tst_bit(uint32_t *b, uint32_t i) {
  uint32_t k, r;

  k = i >> 5;
  r = i & 0x1f;
  return (b[k] & (((uint32_t) 1) << r)) != 0;
}




/*
 * Check whether b1 is a subset of b2
 * - both must have the same size
 */
static bool word_array_subset(uint32_t *b1, uint32_t *b2, uint32_t n) {
  uint32_t i, w;

  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    if ((b1[i] & ~b2[i]) != 0) {
      return false;
    }
  }

  return true;
}


/*
 * Check whether b1 and b2 are disjoint
 */
static bool word_array_disjoint(uint32_t *b1, uint32_t *b2, uint32_t n) {
  uint32_t i, w;

  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    if ((b1[i] & b2[i]) != 0) {
      return false;
    }
  }

  return true;
}



/*
 * Add b2 to b1 (build the union in b1)
 */
static void word_array_add(uint32_t *b1, uint32_t *b2, uint32_t n) {
  uint32_t i, w;

  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    b1[i] |= b2[i];
  }
}


/*
 * Remove b2 from b1
 */
static void word_array_remove(uint32_t *b1, uint32_t *b2, uint32_t n) {
  uint32_t i, w;

  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    b1[i] &= ~b2[i];
  }
}




/*
 * SETS
 */

/*
 * Initialize and reset set dsize to 0
 */
void init_cset(cset_t *s) {
  s->dsize = 0;
  s->hash = 0;
  s->data = NULL;
}

void delete_cset(cset_t *s) {
  safe_free(s->data);
  s->data = NULL;
}

void reset_cset(cset_t *s) {
  s->dsize = 0;
  s->hash = 0;
  safe_free(s->data);
  s->data = NULL;
}



/*
 * Set the domain size to n
 * - must be done after init or reset and before any other operation
 */
static void cset_init_dsize(cset_t *s, uint32_t n) {
  assert(0 < n && s->dsize == 0 && s->data == NULL);
  s->dsize = n;
  if (n > 32) {
    s->data = alloc_word_array(n);
  }
}


/*
 * Empty s
 */
void cset_empty(cset_t *s) {
  uint32_t n;

  assert(s->dsize > 0);

  n = s->dsize;
  s->hash = 0;
  if (n > 32) {
    assert(s->data != NULL);
    clear_word_array(s->data, n);
  }
}


/*
 * Add [0 ... dsize-1] to s
 */
void cset_fill(cset_t *s) {
  uint32_t n;

  assert(s->dsize > 0);

  n = s->dsize;
  if (n <= 32) {
    s->hash = ((uint32_t) 0xffffffff) >> (32 - n);
  } else {
    assert(s->data != NULL);
    s->hash = (uint32_t) 0xffffffff;
    set_word_array(s->data, n);
  }
}


/*
 * initialize to the emptyset, domain [0 ... n-1]
 */
void cset_init_empty(cset_t *s, uint32_t n) {
  cset_init_dsize(s, n);
  cset_empty(s);
}


/*
 * initialize to the full set = [0 ... n-1]
 */
void cset_init_full(cset_t *s, uint32_t n) {
  cset_init_dsize(s, n);
  cset_fill(s);
}


/*
 * Cardinality
 */
uint32_t cset_card(cset_t *s) {
  uint32_t n;

  assert(s->dsize > 0);

  n = s->dsize;
  return (n <= 32) ? popcount32(s->hash) : word_array_popcount(s->data, n);
}



/*
 * Check whether i is in set s
 * - i must be in the domain
 */
bool cset_member(cset_t *s, uint32_t i) {
  assert(i < s->dsize);
  return (s->dsize <= 32) ? (s->hash & (((uint32_t) 1) << i)) : word_array_tst_bit(s->data, i);
}


/*
 * Check whether s1 is included in s2
 */
bool cset_subset(cset_t *s1, cset_t *s2) {
  uint32_t n;

  assert(s1->dsize == s2->dsize && s1->dsize > 0);

  if ((s1->hash & ~s2->hash) != 0) {
    return false;
  }

  n = s1->dsize;
  return n <= 32 || word_array_subset(s1->data, s2->data, n);
}


/*
 * Check whether s1 and s2 are disjoint
 */
bool cset_disjoint(cset_t *s1, cset_t *s2) {
  uint32_t n;

  assert(s1->dsize == s2->dsize && s1->dsize > 0);

  if ((s1->hash & s2->hash) == 0) {
    return true;
  }

  n = s1->dsize;
  return n>32 && word_array_disjoint(s1->data, s2->data, n);
}


/*
 * Add element i
 */
void cset_add(cset_t *s, uint32_t i) {
  assert(i < s->dsize);
  if (s->dsize <= 32) {
    s->hash |= (((uint32_t) 1) << i);
  } else {
    assert(s->data != NULL);
    word_array_set_bit(s->data, i);
    s->hash |= (((uint32_t) 1) << (i & 0x1f));
  }
}


/*
 * Remove element i
 */
void cset_remove(cset_t *s, uint32_t i) {
  assert(i < s->dsize);

  if (s->dsize <= 32) {
    s->hash &= ~(((uint32_t) 1) << i);
  } else {
    assert(s->data != NULL);
    word_array_clr_bit(s->data, i);
    s->hash = hash_word_array(s->data, s->dsize);
  }
}


/*
 * Add s1 to s
 */
void cset_add_set(cset_t *s, cset_t *s1) {
  uint32_t n;

  assert(s->dsize == s1->dsize && s->dsize > 0);

  s->hash |= s1->hash;
  n = s->dsize;
  if (n > 32) {
    word_array_add(s->data, s1->data, n);
  }
}


/*
 * Remove s1 from s2
 */
void cset_remove_set(cset_t *s, cset_t *s1) {
  uint32_t n;

  assert(s->dsize == s1->dsize && s->dsize > 0);

  n = s->dsize;
  if (n <= 32) {
    s->hash &= ~s1->hash;
  } else {
    word_array_remove(s->data, s1->data, n);
    s->hash = hash_word_array(s->data, n);
  }
}


/*
 * Add a[0 ... n-1] to s
 */
void cset_add_array(cset_t *s, uint32_t *a, uint32_t n) {
  uint32_t i, j;

  assert(s->dsize > 0);

  if (s->dsize <= 32) {
    for (i=0; i<n; i++) {
      j = a[i];
      assert(j < s->dsize);
      s->hash |= ((uint32_t) 1) << j;
    }
  } else {
    for (i=0; i<n; i++) {
      j = a[i];
      assert(j < s->dsize);
      word_array_set_bit(s->data, j);
    }
    s->hash = hash_word_array(s->data, s->dsize);
  }
}


/*
 * Remove a[0 ... n-1] from s
 */
void cset_remove_array(cset_t *s, uint32_t *a, uint32_t n) {
  uint32_t i, j;

  assert(s->dsize > 0);

  if (s->dsize <= 32) {
    for (i=0; i<n; i++) {
      j = a[i];
      assert(j < s->dsize);
      s->hash &= ~(((uint32_t) 1) << j);
    }
  } else {
    for (i=0; i<n; i++) {
      j = a[i];
      assert(j < s->dsize);
      word_array_clr_bit(s->data, j);
    }
    s->hash = hash_word_array(s->data, s->dsize);
  }
}


/*
 * Copy the elements of s into vector v
 * - v is not reset: elements are added at the end of v
 */
void cset_extract(cset_t *s, ivector_t *v) {
  uint32_t i, n, mask;

  assert(s->dsize > 0);

  n = s->dsize;
  if (n <= 32) {
    mask = 1;
    for (i=0; i<n; i++) {
      if ((s->hash & mask) != 0) {
	ivector_push(v, i);
      }
      mask <<= 1;
    }
  } else {
    for (i=0; i<n; i++) {
      if (word_array_tst_bit(s->data, i)) {
	ivector_push(v, i);
      }
    }
  }
}
