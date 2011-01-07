/*
 * Buffer for construction of bitvector polynomials
 */

#include <assert.h>
#include <stdbool.h>

#include "prng.h"
#include "memalloc.h"
#include "bv_constants.h"
#include "bit_tricks.h"
#include "bvpoly_buffer.h"


/***********************
 *  CREATION/DELETION  *
 **********************/

/*
 * Initialize buffer
 * - i_size and m_size are initialized to the default
 * - bitsize is set to 0
 * - w_size is 0
 */
void init_bvpoly_buffer(bvpoly_buffer_t *buffer) {
  int32_t *tmp;
  uint32_t i, n;

  assert(DEF_BVPOLYBUFFER_ISIZE < MAX_BVPOLYBUFFER_ISIZE &&
	 DEF_BVPOLYBUFFER_SIZE < MAX_BVPOLYBUFFER_SIZE);

  n = DEF_BVPOLYBUFFER_ISIZE;
  tmp = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    tmp[i] = -1;
  }
  buffer->index = tmp;
  buffer->i_size = n;

  n = DEF_BVPOLYBUFFER_SIZE;
  buffer->var = (thvar_t *) safe_malloc(n * sizeof(thvar_t));
  buffer->c = (uint64_t *) safe_malloc(n * sizeof(uint64_t));
  buffer->m_size = n;

  buffer->p = NULL; // allocated only if needed
  buffer->w_size = 0;

  buffer->nterms = 0;
  buffer->bitsize = 0;
  buffer->width = 0;
}


/*
 * Delete: free memory
 */
void delete_bvpoly_buffer(bvpoly_buffer_t *buffer) {
  uint32_t **p;
  uint32_t i, n;

  safe_free(buffer->index);
  safe_free(buffer->var);
  safe_free(buffer->c);

  buffer->index = NULL;
  buffer->var = NULL;
  buffer->c = NULL;
  
  p = buffer->p;
  if (p != NULL) {
    n = buffer->m_size;
    for (i=0; i<n; i++) {
      safe_free(p[i]);
    }
    safe_free(p);
    buffer->p = NULL;
  }
}


/*
 * Allocate the internal p array if it's NULL
 * - its size is buffer->m_size
 * - all its elements are initialized to NULL
 */
static void bvpoly_alloc_coeff_array(bvpoly_buffer_t *buffer) {
  uint32_t **p;
  uint32_t i, n;

  p = buffer->p; 
  if (p == NULL) {
    n = buffer->m_size;
    p = (uint32_t **) safe_malloc(n * sizeof(uint32_t *));
    for (i=0; i<n; i++) {
      p[i] = NULL;
    }
    buffer->p = p;
  }
}


/*
 * Free all elements of array p
 * - this is used when they are too small for the current width
 */
static void bvpoly_reset_coeff_array(bvpoly_buffer_t *buffer) {
  uint32_t **p;
  uint32_t i, n;

  p = buffer->p;
  assert(p != NULL);

  n = buffer->m_size;
  for (i=0; i<n; i++) {
    if (p[i] == NULL) break;
    safe_free(p[i]);
    p[i] = NULL;
  }
}


/*
 * Reset buffer and prepare for construction of a polynomial
 * with the given bitsize.
 * - bitsize must be positive
 * - allocate the p vector if bitsize > 64
 * - make sure the w_size is large enough
 */
void reset_bvpoly_buffer(bvpoly_buffer_t *buffer, uint32_t bitsize) {
  uint32_t w, w_size;
  uint32_t i, n;
  thvar_t x;

  assert(bitsize > 0);

  w = (bitsize + 31) >> 5;
  buffer->bitsize = bitsize;
  buffer->width = w;

  // clear the variable indices
  n = buffer->nterms;
  for (i=0; i<n; i++) {
    x = buffer->var[i];
    assert(buffer->index[x] == i);
    buffer->index[x] = -1;
  }
  buffer->nterms = 0;

  if (bitsize > 64) {
    bvpoly_alloc_coeff_array(buffer);
    w_size = buffer->w_size;
    if (w_size < w) {
      bvpoly_reset_coeff_array(buffer);
      // new w_size = max(2 * current w_size, w)
      w_size <<= 1;
      if (w_size < w) {
	w_size = w;
      }
      buffer->w_size = w_size;
    }
  }
}




/*
 * Extend the index array and initialize new elements to -1
 * - this makes sure the index array is large enough to store index[x]
 * - x must be >= buffer->i_size
 */
static void bvpoly_buffer_resize_index(bvpoly_buffer_t *buffer, thvar_t x) {
  int32_t *tmp;
  uint32_t i, n;

  assert(buffer->i_size <= x && x < max_idx);

  // the new size is max(1.5 * current_size, x +1)
  n = buffer->i_size;
  n += n>>1;
  if (n <= x) {
    n = x+1;
  }

  if (n >= MAX_BVPOLYBUFFER_ISIZE) {
    out_of_memory();
  }

  tmp = (int32_t *) safe_realloc(buffer->index, n * sizeof(int32_t));
  for (i=buffer->i_size; i<n; i++) {
    tmp[i] = -1;
  }

  buffer->index = tmp;
  buffer->i_size = n;
}




/*
 * Increase the size of arrays var and c, and p if it's non NULL.
 * Also increase the sign bitarray
 * - if p is non-null, the new elements of p are initialized to NULL
 */
static void bvpoly_buffer_extend_mono(bvpoly_buffer_t *buffer) {
  uint32_t **p;
  uint32_t i, n;

  n = buffer->m_size + 1;
  n += n>>1;
  if (n >= MAX_BVPOLYBUFFER_SIZE) {
    out_of_memory();
  }

  buffer->var = (thvar_t *) safe_realloc(buffer->var, n * sizeof(thvar_t));
  buffer->c = (uint64_t *) safe_realloc(buffer->c, n * sizeof(uint64_t));

  p = buffer->p;
  if (p != NULL) {
    p = (uint32_t **) safe_realloc(p, n * sizeof(uint32_t *));
    for (i=buffer->m_size; i<n; i++) {
      p[i] = NULL;
    }
    buffer->p = p;
  }

  buffer->m_size = n;
}



/*
 * Allocate a new monomial and return its index i
 * - if needed, make the var, c, and p arrays larger
 * - set the coefficient c[i] or p[i] to 0
 *   (also allocate a large enough array p[i])
 */
static int32_t bvpoly_buffer_alloc_mono(bvpoly_buffer_t *buffer) {
  uint32_t i;
  
  i = buffer->nterms;
  if (i == buffer->m_size) {
    bvpoly_buffer_extend_mono(buffer);
  }
  assert(i < buffer->m_size);

  if (buffer->bitsize > 64) {
    assert(buffer->p != NULL);
    if (buffer->p[i] == NULL) {
      buffer->p[i] = (uint32_t *) safe_malloc(buffer->w_size * sizeof(uint32_t));
    }
  }
  
  buffer->nterms = i+1;

  return i;
}


/*
 * Get buffer->index[x] (resize the index array if needed)
 */
static inline int32_t bvpoly_buffer_get_index(bvpoly_buffer_t *buffer, thvar_t x) {
  assert(0 <= x && x < max_idx);
  if (x >= buffer->i_size) {
    bvpoly_buffer_resize_index(buffer, x);
  }
  return buffer->index[x];
}



/************************
 *  MONOMIAL ADDITION   *
 ***********************/

/*
 * Add monomial a * x to buffer
 * - buffer->bitsize must be no more than 64
 */
void bvpoly_buffer_add_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a) {
  int32_t i;

  assert(0 < buffer->bitsize && buffer->bitsize <= 64);

  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x);
    buffer->c[i] += a;
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    buffer->c[i] = a;
  }
}


/*
 * Subtract monomial a * x from buffer
 * - buffer->bitsize must be no more than 64
 */
void bvpoly_buffer_sub_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a) {
  int32_t i;

  assert(0 < buffer->bitsize && buffer->bitsize <= 64);

  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x);
    buffer->c[i] -= a;
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    buffer->c[i] = -a; // 2-complement
  }
}


/*
 * Add a * b * x to buffer
 * - buffer->bitsize must be no more than 64
 */
void bvpoly_buffer_addmul_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a, uint64_t b) {
  int32_t i;

  assert(0 < buffer->bitsize && buffer->bitsize <= 64);

  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x);
    buffer->c[i] += a * b;
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    buffer->c[i] = a * b;
  }
}


/*
 * Subtract a * b * x from buffer
 * - buffer->bitsize must be no more than 64
 */
void bvpoly_buffer_submul_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a, uint64_t b) {
  int32_t i;

  assert(0 < buffer->bitsize && buffer->bitsize <= 64);

  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x);
    buffer->c[i] -= a * b;
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    buffer->c[i] = -(a * b);
  }
}






/*
 * Add monomial a * x to buffer
 * - buffer->bitsize must be more than 64
 * - a must be an array of w words (where w = ceil(bitsize / 32)
 */
void bvpoly_buffer_add_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a) {
  uint32_t w;
  int32_t i;

  assert(64 < buffer->bitsize);
  w = buffer->width;
  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x && buffer->p[i] != NULL);
    bvconst_add(buffer->p[i], w, a);
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    bvconst_set(buffer->p[i], w, a);
  }
}


/*
 * Subtract monomial a * x from buffer
 * - buffer->bitsize must be more than 64
 * - a must be an array of w words (where w = ceil(bitsize / 32)
 */
void bvpoly_buffer_sub_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a) {
  uint32_t w;
  int32_t i;

  assert(64 < buffer->bitsize);
  w = buffer->width;
  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x && buffer->p[i] != NULL);
    bvconst_sub(buffer->p[i], w, a);
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    bvconst_negate2(buffer->p[i], w, a);
  }
}

/*
 * Add monomial a * b * x to buffer
 * - buffer->bitsize must be more than 64
 * - a and b must be arrays of w words (where w = ceil(bitsize / 32)
 */
void bvpoly_buffer_addmul_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a, uint32_t *b) {
  uint32_t w;
  int32_t i;

  assert(64 < buffer->bitsize);
  w = buffer->width;
  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x && buffer->p[i] != NULL);
    bvconst_addmul(buffer->p[i], w, a, b);
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    bvconst_clear(buffer->p[i], w);
    bvconst_addmul(buffer->p[i], w, a, b);
  }
}


/*
 * Subtract monomial a * b * x from buffer
 * - buffer->bitsize must be more than 64
 * - a and b must be arrays of w words (where w = ceil(bitsize / 32)
 */
void bvpoly_buffer_submul_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a, uint32_t *b) {
  uint32_t w;
  int32_t i;

  assert(64 < buffer->bitsize);
  w = buffer->width;
  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x && buffer->p[i] != NULL);
    bvconst_submul(buffer->p[i], w, a, b);
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    bvconst_clear(buffer->p[i], w);
    bvconst_submul(buffer->p[i], w, a, b);
  }
}





/*
 * Add x to buffer (i.e., monomial 1 * x)
 */
void bvpoly_buffer_add_var(bvpoly_buffer_t *buffer, thvar_t x) {
  uint32_t w;
  int32_t i;

  w = buffer->width;
  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x);
    if (w < 2) {
      buffer->c[i] ++;
    } else {
      bvconst_add_one(buffer->p[i], w);
    }
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    if (w < 2) {
      buffer->c[i] = 1;
    } else {
      bvconst_set_one(buffer->p[i], w);
    }
  }
}



/*
 * Subtract x from buffer (i.e., monomial 1 * x)
 */
void bvpoly_buffer_sub_var(bvpoly_buffer_t *buffer, thvar_t x) {
  uint32_t w;
  int32_t i;

  w = buffer->width;
  i = bvpoly_buffer_get_index(buffer, x);
  if (i >= 0) {
    assert(i < buffer->nterms && buffer->var[i] == x);
    if (w < 2) {
      buffer->c[i] --;
    } else {
      bvconst_sub_one(buffer->p[i], w);
    }
  } else {
    i = bvpoly_buffer_alloc_mono(buffer);
    buffer->index[x] = i;
    buffer->var[i] = x;
    if (w < 2) {
      buffer->c[i] = ((uint64_t) -1);
    } else {
      bvconst_set_minus_one(buffer->p[i], w);
    }
  }
}



/*******************
 *  NORMALIZATION  *
 ******************/


/*
 * Utility for sorting: swap monomials at indices i and j
 */
static void swap_monomials(bvpoly_buffer_t *buffer, uint32_t i, uint32_t j) {
  thvar_t x, y;
  uint64_t aux;
  uint32_t *p;

  assert(i < buffer->nterms && j < buffer->nterms);

  x = buffer->var[i];
  y = buffer->var[j];

  assert(buffer->index[x] == i && buffer->index[y] == j);

  buffer->index[x] = j;
  buffer->index[y] = i;
  buffer->var[i] = y;
  buffer->var[j] = x;
  if (buffer->bitsize <= 64) {
    aux = buffer->c[i];
    buffer->c[i] = buffer->c[j];
    buffer->c[j] = aux;
  } else {
    p = buffer->p[i];
    buffer->p[i] = buffer->p[j];
    buffer->p[j] = p;
  }
}



/*
 * SORT
 */

/*
 * Sort monomials at indices between l and (h-1)
 * - use inserion or quicksort
 */
static void sort_buffer(bvpoly_buffer_t *buffer, uint32_t l, uint32_t h);

/*
 * Insertion sort
 */
static void isort_buffer(bvpoly_buffer_t *buffer, uint32_t l, uint32_t h) {
  uint32_t i, j;
  thvar_t x;

  assert(l <= h);

  for (i=l+1; i<h; i++) {
    x = buffer->var[i];
    j = i;
    do {
      j --;
      if (buffer->var[j] < x) break;
      swap_monomials(buffer, j, j+1);
    } while (j > l);
  }
}

/*
 * Quick sort: requires h > l
 */
static void qsort_buffer(bvpoly_buffer_t *buffer, uint32_t l, uint32_t h) {
  uint32_t i, j;
  thvar_t x;

  assert(h > l);

  // random pivot
  i = l + random_uint(h - l);

  // move it to position l
  swap_monomials(buffer, i, l);
  x = buffer->var[l];
  
  i = l;
  j = h;
  do { j--; } while (buffer->var[j] > x);
  do { i++; } while (i <= j && buffer->var[i] < x);

  while (i < j) {
    swap_monomials(buffer, i, j);
    do { j--; } while (buffer->var[j] > x);
    do { i++; } while (buffer->var[i] < x);
  }

  // swap pivot and monomial j
  swap_monomials(buffer, l, j);

  sort_buffer(buffer, l, j);
  sort_buffer(buffer, j+1, h);
}


static void sort_buffer(bvpoly_buffer_t *buffer, uint32_t l, uint32_t h) {
  if (h < l + 4) {
    isort_buffer(buffer, l, h);
  } else {
    qsort_buffer(buffer, l, h);
  }
}



/*
 * Sort all monomials
 */
static inline void poly_buffer_sort(bvpoly_buffer_t *buffer) {
  sort_buffer(buffer, 0, buffer->nterms);
}



/*
 * AFTER SORTING
 */

/*
 * Reduce all coefficients modulo 2^bitsize
 * - remove the zero coefficients
 */
static void bvpoly_buffer_reduce_coefficients(bvpoly_buffer_t *buffer) {
  uint32_t *p;
  uint64_t mask;
  uint32_t i, j, n, b, w;
  thvar_t x;
  

  b = buffer->bitsize;
  n = buffer->nterms;
  if (b > 64) {
    /*
     * Large coefficients
     */
    w = buffer->width;
    j = 0;
    for (i=0; i<n; i++) {
      assert(j <= i);
      x = buffer->var[i];
      p = buffer->p[i];
      bvconst_normalize(p, b);
      if (bvconst_is_zero(p, w)) {
	// remove monomial i
	buffer->index[x] = -1;
      } else {
	if (j < i) {
	  // move monomial i to position j
	  buffer->index[x] = j;
	  buffer->var[j] = x;
	  buffer->p[i] = buffer->p[j]; // swap rather than copy p[i] into p[j]
	  buffer->p[j] = p;
	}
	j ++;
      }      
    }
    buffer->nterms = j;

  } else {
    /*
     * Small coefficients
     */
    mask = (~((uint64_t) 0)) >> (64 - b);
    j = 0;
    for (i=0; i<n; i++) {
      assert(j <= i);
      x = buffer->var[i];
      buffer->c[i] &= mask; // clear high-order bits
      if (buffer->c[i] == 0) {
	// remove monomial i
	buffer->index[x] = -1;
      } else {
	if (j < i) {
	  // move monomial i to position j
	  buffer->index[x] = j;
	  buffer->var[j] = x;
	  buffer->c[j] = buffer->c[i];
	}
	j ++;
      }
    }
    buffer->nterms = j;
  }
}



/*
 * Set the coefficient signs and negate coefficients if that's
 * avantageous. Fewer 1 bits in 'a' means fewer adders 
 * to represent 'a * x', when that gets converted to a circuit).
 * 
 * Heuristics (used if coefficients are large)
 * ----------
 * If popcount(a) = k and a has n bits then popcount(-a) <= (n - k) + 1.
 * More precisely, we have
 * - popcount(-a) = (n - k) + 1 if lowest order bit of a is 1,
 * - popcount(-a) <= (n - k) if lowest order bit of a is 0
 * So it saves to replace a by -a if 2k > n + lower bit of a
 *
 * This must be done after reducing the coefficients modulo 2^n
 */
static void bvpoly_buffer_reduce_ones(bvpoly_buffer_t *buffer) {
  uint32_t *p;
  uint64_t mask, a;
  uint32_t i, n, w, b, k;

  b = buffer->bitsize;
  n = buffer->nterms;  
  if (b > 64) {
    /*
     * Large coefficients
     */
    w = buffer->width;
    for (i=0; i<n; i++) {
      p = buffer->p[i];
      k = bvconst_popcount(p, w);
      assert(1 <= k && k <= b);
      if (2 * k > b + bvconst_tst_bit(p, 0)) {
	// negate coefficient and set the sign bit
	bvconst_negate(p, w);
	bvconst_normalize(p, b);
	set_bit(buffer->sign, i);
      } else {
	// do nothing: clear the sign bit
	clr_bit(buffer->sign, i);
      }
      assert(bvconst_popcount(p, w) <= (b+1)/2);
    }
  } else {
    /*
     * Small coefficients
     */
    mask = (~((uint64_t) 0)) >> (64 - b);
    for (i=0; i<n; i++) {
      a = buffer->c[i];
      k = popcount64(a);
      assert(1 <= k && k <= b);
      // compare with opposite of a
      a = (-a) & mask;      
      if (popcount64(a) < k) {
	// use the negative coeff + set the sign bit
	buffer->c[i] = a;
	set_bit(buffer->sign, i);
      } else {
	// clear the sign bit
	clr_bit(buffer->sign, i);
      }
      assert(popcount64(buffer->c[i]) <= (b+1)/2);
    }
  }
}


/*
 * Normalize buffer:
 * - normalize all the coefficients (reduce them modulo 2^n where n = bitsize)
 * - replace coeff a by -a if (-a) has fewer 1-bits than a 
 *   (e.g., if a is 0b111...1, then it's replaced by - 0b000001)
 * - sort the terms in increasing order of variables
 *   (the constant term comes first if any)
 * - remove all terms with a zero coefficient
 */
void normalize_bvpoly_buffer(bvpoly_buffer_t *buffer) {
  poly_buffer_sort(buffer);
  bvpoly_buffer_reduce_coefficients(buffer);  
  bvpoly_buffer_reduce_ones(buffer);
}



