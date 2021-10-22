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
 * SPARSE ARRAYS
 */

#include "utils/memalloc.h"
#include "utils/sparse_arrays.h"


/*
 * Initialize a:
 * - n = minimal size requested
 * - if n is 0, the default size is used
 * - all blocks are marked as clean
 */
void init_sparse_array(sparse_array_t *a, uint32_t n) {
  uint32_t nblocks;

  if (n == 0) {
    nblocks = DEF_SPARSE_ARRAY_NBLOCKS;
  } else {
    nblocks = (n + (BSIZE - 1)) >> BSIZE_NBITS;
    assert(n <= nblocks * BSIZE);
    if (nblocks > MAX_NBLOCKS) {
      out_of_memory();
    }
  }

  // adjust n to a multiple of the block size
  n = nblocks * BSIZE;
  a->data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  a->clean = allocate_bitvector0(nblocks); // all dirty
  a->nblocks = nblocks;
  a->nelems = 0;
}


/*
 * Delete: free all memory
 */
void delete_sparse_array(sparse_array_t *a) {
  safe_free(a->data);
  delete_bitvector(a->clean);
  a->data = NULL;
  a->clean = NULL;
}


/*
 * Reset: mark all blocks as dirty
 */
void reset_sparse_array(sparse_array_t *a) {
  clear_bitvector(a->clean, a->nblocks);
  a->nelems = 0;
}


/*
 * Initialize block i in array a
 */
static void clean_block(uint32_t *a, uint32_t i) {
  uint32_t n;

  n = BSIZE;
  a += block_start(i);
  do {
    *a ++ = 0;
    n --;
  } while (n > 0);
}


/*
 * Copy block i of a into b
 */
static void copy_block(uint32_t *b, uint32_t *a, uint32_t i) {
  uint32_t n;

  n = BSIZE;
  a += block_start(i);
  b += block_start(i);
  do {
    * b++ = *a ++;
    n --;
  } while (n > 0);
}



/*
 * Resize the array to at least nb blocks
 * - nb must be more than a->nblocks
 */
static void resize_sparse_array(sparse_array_t *a, uint32_t nb) {
  uint32_t i, nblocks, n;
  uint32_t *tmp;

  if (nb > MAX_NBLOCKS) {
    out_of_memory();
  }

  n = a->nblocks;
  nblocks = n;
  nblocks += nblocks>>1; // try 50% larger
  if (nb > nblocks) {
    nblocks = nb;
  } else if (nblocks > MAX_NBLOCKS) {
    nblocks = MAX_NBLOCKS;
  }

  // n = current size, nblocks = new size
  // we avoid realloc here (to save the cost of copying the full array)
  tmp = (uint32_t *) safe_malloc(nblocks * (BSIZE * sizeof(uint32_t)));
  a->clean = extend_bitvector0(a->clean, nblocks, n);

  // copy all clean blocks from a->data to tmp
  n = a->nblocks;
  for (i=0; i<n; i++) {
    if (tst_bit(a->clean, i)) {
      copy_block(tmp, a->data, i);
    }
  }

  safe_free(a->data);
  a->data = tmp;
  a->nblocks = nblocks;
}


/*
 * Read the value mapped to i:
 * - return 0 if i is in a dirty block or outside the array
 */
uint32_t sparse_array_read(sparse_array_t *a, uint32_t i) {
  uint32_t k, y;

  k = block_of_index(i);
  y = 0;
  if (k < a->nblocks && tst_bit(a->clean, k)) {
    y = a->data[i];
  }
  return y;
}


/*
 * Increment a[i]
 */
void sparse_array_incr(sparse_array_t *a, uint32_t i) {
  uint32_t k;

  k = block_of_index(i);
  if (k >= a->nblocks) {
    resize_sparse_array(a, k+1);
  }
  if (tst_bit(a->clean, k) && a->data[i] < UINT32_MAX) {
    if (a->data[i] == 0) {
      a->nelems ++;
    }
    a->data[i] ++;
  } else {
    set_bit(a->clean, k);
    clean_block(a->data, k);
    a->data[i] = 1;
    a->nelems ++;
  }
}


/*
 * Decrement a[i]: the current count must be positive
 */
void sparse_array_decr(sparse_array_t *a, uint32_t i) {
#ifndef NDEBUG
  uint32_t k;

  k = block_of_index(i);
  assert(k < a->nblocks && tst_bit(a->clean, k) && a->data[i] > 0);
#endif

  a->data[i] --;
  if (a->data[i] == 0) {
    assert(a->nelems > 0);
    a->nelems --;
  }
}


/*
 * Apply f(aux, i) to all i that have positive count in block k
 */
static void iterate_in_block(uint32_t *a, uint32_t k, void *aux, sparse_array_iterator_t f) {
  uint32_t n, i;

  n = block_start(k) + BSIZE;
  for (i = block_start(k); i<n; i++) {
    if (a[i] > 0) {
      f(aux, i);
    }
  }
}


/*
 * Go through all elements i with a positive ref counter and call f(aux, i)
 */
void sparse_array_iterate(sparse_array_t *a, void *aux, sparse_array_iterator_t f) {
  uint32_t i, n;

  n = a->nblocks;
  for (i=0; i<n; i++) {
    if (tst_bit(a->clean, i)) {
      iterate_in_block(a->data, i, aux, f);
    }
  }
}

