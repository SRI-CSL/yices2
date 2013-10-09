/*
 * STABLE-SORT
 */

#include <assert.h>
#include <string.h>
#include <stdlib.h>

#include "stable_sort.h"


/*
 * Initialize sorter:
 * - cmp = ordering function
 * - aux = auxiliary object
 * - data is set to NULL and nelems to 0
 */
void init_stable_sorter(stable_sorter_t *sorter, void *aux, cmp_fun_t cmp) {
  sorter->data  = NULL;
  sorter->nelems = 0;
  sorter->cmp = cmp;
  sorter->aux = aux;

  sorter->seg[0] = 0;
  sorter->nsegs = 0;
  sorter->buffer = sorter->b;
  sorter->bsize = FIXED_BUFFER_SIZE;
}


/*
 * Delete: free all internal memory
 */
void delete_stable_sorter(stable_sorter_t *sorter) {
  if (sorter->bsize > FIXED_BUFFER_SIZE) {
    free(sorter->buffer);
  }
  sorter->buffer = NULL;
}



/*
 * Copy data[i ... j-1] into the buffer:
 * - if the buffer is too small, attempt to resize it. If that fails,
 *   do nothing and return false.
 * - return true otherwise
 */
static bool move_to_buffer(stable_sorter_t *sorter, uint32_t i, uint32_t j) {
  void **tmp;
  uint32_t n;

  n = j - i;
  if (n > sorter->bsize) {
    // need a bigger buffer
    if (n > MAX_BUFFER_SIZE) return false;
    tmp = (void **) malloc(n * sizeof(void *));
    if (tmp == NULL) return false;

    // malloc worked
    if (sorter->bsize > FIXED_BUFFER_SIZE) {
      free(sorter->buffer);
    }
    sorter->buffer = tmp;
    sorter->bsize = n;
  }
  memcpy(sorter->buffer, sorter->data + i, n * sizeof(void*));

  return true;
}



/*
 * Mimimal run size for an array of size n:
 * - returns n if n < 64
 * - returns 32 if n is a power of two
 * - returns a number between 33 and 64 otherwise = 
 *   1 + the 6 high order bits of n
 */
static uint32_t min_run(uint32_t n) {
  uint32_t r;

  r = 0;
  while (n >= 64) {
    r |= n & 1u;
    n >>= 1;
  }
  return n + r;
}


/*
 * Binary search: locate the position of p in slice data[i .. j-1]
 * - the slice data[i ... j-1] must be sorted
 * - this returns k such that i <= k <= j and 
 * - all elements in data[i ... k-1] are less than or equal to p
 * - all elements in data[k ... j-1] are strictly more than p
 *
 * In particular:
 * - if all elements are more than p --> return i
 * - if all elements are less than or equal to p --> return j
 */
static uint32_t locate_left(stable_sorter_t *sorter, uint32_t i, uint32_t j, void *p) {
  void **a;
  uint32_t k;

  assert(i <= j && j <= sorter->nelems);

  a = sorter->data;
  while (i < j) {
    k = i + ((j - i) >> 1);
    assert(i <= k && k < j);
    if (sorter->cmp(sorter->aux, a[k], p)) {
      i = k+1;
    } else {
      j = k;
    }
  }

  return i;
}


/*
 * Binary search variant:
 * - return k such that i <= k <= j and
 * - all elements in data[i ... k-1] are strictly less than p
 * - all elements in data[k ... j-1] are more than or equal to p
 */
static uint32_t locate_right(stable_sorter_t *sorter, uint32_t i, uint32_t j, void *p) {
  void **a;
  uint32_t k;
 
  assert(i <= j && j <= sorter->nelems);

  a = sorter->data;
  while (i < j) {
    k = i + ((j - i) >> 1);
    assert(i <= k && k < j);
    if (sorter->cmp(sorter->aux, p, a[k])) {
      j = k;
    } else {
      i = k+1;
    }
  }

  return i;
}


/*
 * Insertion sort of data[i ... k-1]
 * - data[i .. j-1] is already sorted
 * - j may be equal to k
 */
static void binary_isort(stable_sorter_t *sorter, uint32_t i, uint32_t j, uint32_t k) {
  void **a;
  void *p;
  uint32_t t, u;

  assert(i <= j && j <= k && k <= sorter->nelems);

  a = sorter->data;
  while (j < k) {
    p = sorter->data[j];
    t = locate_left(sorter, i, j, p);
    u = j;
    while (t < u) {
      a[u] = a[u-1];
      u --;
    }
    a[u] = p;
    j ++;
  }
}


/*
 * Reverse the slice data[i ... j-1]
 * - requires i < j
 */
static void reverse_slice(stable_sorter_t *sorter, uint32_t i, uint32_t j) {
  void **a;
  void *p;

  assert(i < j && j <= sorter->nelems);

  a = sorter->data;

  j --;
  while (i < j) {
    p = a[i];
    a[i] = a[j];
    a[j] = p;
    i ++;
    j --;
  }
}


/*
 * Search for the longest run starting at i
 * - set *increasing to true if the run is increasing
 * - set *increasing to false otherwise (strictly decreasing)
 * - return the end of the run: index j such that data[i ... j-1] is the run
 */
static uint32_t find_run(stable_sorter_t *sorter, uint32_t i, bool *increasing) {
  void **a;
  uint32_t n;

  assert(i < sorter->nelems);

  a = sorter->data;
  n = sorter->nelems;
  i ++;
  if (i == n) {
    // single element run
    *increasing = true;
  } else if (sorter->cmp(sorter->aux, a[i-1], a[i])) {
    // increasing run
    *increasing = true;
    do {
      i ++;
    } while (i < n && sorter->cmp(sorter->aux, a[i-1], a[i]));

  } else {
    // strictly decreasing run
    *increasing = false;
    do {
      i ++;
    } while (i < n && !sorter->cmp(sorter->aux, a[i-1], a[i]));
  }

  return i;
}


/*
 * Merge runs data[i ... j-1] and data[j ... k-1] where i < j and j <  k 
 * - this is a slower than merge_left or merge_right but it can be used 
 *   if buffer is too small to contain a full copy of data[i ... j-1] 
 *   or data[j ... k-1]
 */
static void low_mem_merge(stable_sorter_t *sorter, uint32_t i, uint32_t j, uint32_t k) {
  void **a, **b;
  void *p, *q;
  uint32_t t, u, v, s, n;

  assert(i < j && j < k && k <= sorter->nelems);

  a = sorter->data;
  b = sorter->buffer;
  n = sorter->bsize;

  do {
    s = 0;
    t = i;
    u = j;

    /*
     * merge initial elements of a[i ... j-1] and a[j .. k-1] 
     * into the buffer: b[0 ... n-1]
     */
    do {
      assert(i <= t && t < j && j <= u && u < k && s < n);

      p = a[t];
      q = a[u];
      if (sorter->cmp(sorter->aux, p, q)) {
	b[s] = p;
	s ++;
	t ++;
      } else {
	b[s] = q;
	s ++;
	u ++;
      }
    } while (s < n && t < j && u < k);

    assert(s == (t - i) + (u - j));

    /*
     * b[0 ... s-1] contains the merge of a[i ... t-1] and a[j ... u-1]
     * - move a[t .. j] (what's left of the first run) into a[i+s .. u-1]
     * - then copy buffer into a[i ... i+s]
     */
    v = u;
    while (t < j) {
      j --;
      v --;
      a[v] = a[j];
    }
    assert(v == i+s);

    for (v=0; v<s; v++, i++) {
      a[i] = b[v];
    }
    j = u;    

  } while (i < j && j < k);
}


/*
 * Merge runs data[i ... j-1] and data[j .. k-1]  when (j - i) <= (k - j)
 * - copy the first run data[i ... j-1] into the temporarty buffer then merge
 *   the buffer and data[j ... k-1] into data[i ... k-1]
 * - defaults to low_mem_merge in a large enough temp buffer can't be allocated
 */
static void merge_left(stable_sorter_t *sorter, uint32_t i, uint32_t j, uint32_t k) {
  void **a, **b;
  void *p, *q;
  uint32_t t, n;

  assert(i < j && j < k && k <= sorter->nelems);

  /*
   * move  data[i ... j-1] to the buffer
   * if that fails, use slow merge
   */
  if (! move_to_buffer(sorter, i, j)) {
    low_mem_merge(sorter, i, j, k);
    return;
  } 

  /*
   * merge a[0 ... n-1] = buffer and b[j ... k-1] = data[j .. k-1]
   * into data[i .. k-1].
   */
  a = sorter->buffer;
  b = sorter->data;
  n = j - i;
  t = 0;

  p = a[t];
  q = b[j];

  for (;;) {
    assert(t < n && j < k && i <= j && p == a[t] && q == b[j]);

    if (sorter->cmp(sorter->aux, p, q)) {
      // p <= q: store p into b[i]
      b[i] = p;
      i ++;
      t ++;
      if (t == n) return;
      p = a[t];
    } else {
      // q < p: store q into b[i]
      b[i] = q;
      i ++;
      j ++;
      if (j == k) break;
      q = b[j];
    }
  }

  // copy what's left of a (namely, a[t .. n-1]) into b[i ... k-1]
  assert(t < n && j == k && n - t == k - i);
  do {
    b[i] = a[t];
    i ++;
    t ++; 
  } while (t < n);  
}


/*
 * Merge runs data[i ... j-1] and data[j ... k-1] when (j - i) > (k - j)
 * - copy the second run into the the temporary buffer then
 *   merge the buffer and data[i ... j-1] into data[i ... k-1]
 *   starting with index k-1
 * - defaults to low_mem_merge in a large enough temp buffer can't be allocated
 */
static void merge_right(stable_sorter_t *sorter, uint32_t i, uint32_t j, uint32_t k) {
  void **a, **b;
  void *p, *q;
  uint32_t n;

  assert(i < j && j < k && k <= sorter->nelems);
  
  if (! move_to_buffer(sorter, j, k)) {
    low_mem_merge(sorter, i, j, k);
    return;
  }

  /*
   * a[i ... j-1] = first run
   * b[0 ... n-1] = buffer
   */
  a = sorter->data;
  b = sorter->buffer;
  n = k - j;
  
  n --;
  j --;
  k --;
  p = a[j];
  q = b[n];

  for (;;) {
    assert(0 <= n && i <= j && j <= k && p == a[j] && q == b[n]);

    if (sorter->cmp(sorter->aux, p, q)) {
      // p <= q: store q into a[k]
      a[k] = q;
      k --;
      if (n == 0) return;
      n --;
      q = b[n];
    } else {
      // q < p: store p into a[k]
      a[k] = p;
      k --;
      if (i == j) break;
      j --;
      p = a[j];
    }
  }

  // copy what's left of b (i.e., b[0 .. n]) into a[i ... k])
  // n may be 0 here 
  assert(j == i && k - i == n); 

  a[k] = b[n];
  while (n > 0) {
    k --;
    n --;
    a[k] = b[n];
  }
}


/*
 * Merge the two runs data[i ... j-1] and data[j ... k-1] in place
 * - use temporary buffer
 */
static void merge_runs(stable_sorter_t *sorter, uint32_t i, uint32_t j, uint32_t k) {
  void **a;
  uint32_t i0, j0;

  assert(i < j && j < k && k <= sorter->nelems);

  a = sorter->data;

  /*
   * a[j] = smallest element in the second run
   * i0 = its location in segment a[i ... j-1]
   * a[i ... i0-1] doesn't need to change
   */
  i0 = locate_left(sorter, i, j, a[j]); 
  if (i0 == j) return;
  assert(i <= i0 && i0 < j);

  /*
   * a[j-1] = largest element in the first run
   * j0 = its location in segment a[j ... k-1]
   * a[j0 ... k-1] doesn't change
   */
  j0 = locate_right(sorter, j, k, a[j-1]); // j0 = location of a[j-1] 
  assert(j < j0 && j0 <= k);

  // now we merge data[i0 ... j-1] and data[j ... j0-1]
  if (j - i0 <= j0 - j) {
    merge_left(sorter, i0, j, j0);
  } else {
    merge_right(sorter, i0, j, j0);
  }
}


/*
 * Add a new run to the stack: 
 * - i = start index of the unprocessed part
 * - so we push i on top of the segment stack
 * After the push:
 * - the new segment starts at seg[nsegs-1] and ends sat seg[nsegs]
 */
static void push_segment(stable_sorter_t *sorter, uint32_t i) {
  uint32_t n;

  n = sorter->nsegs;

  assert(n + 1 < MAX_SEGMENTS && sorter->seg[n] < i && i <= sorter->nelems);

  n ++;
  sorter->seg[n] = i;
  sorter->nsegs = n;
}


/*
 * Balance the stack to ensure the invariant:
 *  size of segment i > sum of the sizes of segment i+1 ... nsegs-1
 */
static void balance_runs(stable_sorter_t *sorter) {
  uint32_t n, a, b, c, d;

  n = sorter->nsegs;
  if (n < 2) return;

  d = sorter->seg[n];
  c = sorter->seg[n-1];
  b = sorter->seg[n-2];

  while (n >= 3) {
    a = sorter->seg[n-3];

    assert(a < b && b < c && c < d && d <= sorter->nelems);

    /*
     * the last three runs are [a .. b-1][b .. c-1][c .. d-1]
     * let A = b - a = size of the left segment
     *     B = c - b = size of the middle segment
     *     C = d - c = size of the right segment
     *     B+C = d - b
     *
     * if A <= B+C 
     *   if A < C 
     *      merge left and middle segments
     *   else 
     *      merge middle and right segments.
     */
    if (b - a > d - b) break;

    if (b - a < d - c) {
      // merge left and middle
      merge_runs(sorter, a, b, c);
      sorter->seg[n-2] = c;
    } else {
      // merge middle and right
      merge_runs(sorter, b, c, d);
      c = b;
    }

    b = a;
    sorter->seg[n-1] = d;
    n --;

    assert(n >= 2 && b == sorter->seg[n-2] && c == sorter->seg[n-1] && d == sorter->seg[n]);
  }

  /*
   * Last two segments: [b ... c-1] and [c ... d-1]
   * merge them if B <= C
   */
  if (c - b <= d - c) {
    merge_runs(sorter, b, c, d);
    sorter->seg[n-1] = d;
    n --; 
  }

  sorter->nsegs = n;
}


/*
 * Complete the sort: merge all the segments on the stack
 */
static void merge_all(stable_sorter_t *sorter) {
  uint32_t n, a, b, c;

  n = sorter->nsegs;
  assert(n >= 1);

  c = sorter->seg[n];
  b = sorter->seg[n-1];
  while (n >= 2) {
    a = sorter->seg[n-2];
    assert(a < b && b < c && c <= sorter->nelems);
    merge_runs(sorter, a, b, c);
    b = a;
    n --;
  }
}


/*
 * Sort array a of n elements
 * - sorter must be initialized with the right comparison function
 */
void apply_sorter(stable_sorter_t *sorter, void **a, uint32_t n) {
  uint32_t min, i, j, k;
  bool increasing;

  if (n <= 1) return;

  sorter->data = a;
  sorter->nelems = n;

  assert(sorter->nsegs == 0 && sorter->seg[0] == 0);

  min = min_run(n);
  i = 0; // start of the unprocessed region of data
  while (i < n) {
    j = find_run(sorter, i, &increasing);
    if (!increasing) {
      reverse_slice(sorter, i, j);
    }

    /*
     * The current run is [i ... j-1]
     * If it's too short (less than min elements) extend it to the minimal
     * size using insertion sort.
     */
    k = i + min;
    if (j < k) {
      if (n < k) k = n;
      binary_isort(sorter, i, j, k);
      j = k;
    }

    /*
     * Add the run [i .. j-1] to the stack
     */
    push_segment(sorter, j);
    balance_runs(sorter);
    i = j;
  }

  // finish the sort
  merge_all(sorter);
  
  // reset the stack
  sorter->nsegs = 0;
}


/*
 * Direct stable sort of a using the given comparison function
 * - this initializes then delete an internal sorter object
 */
void stable_sort(void **a, uint32_t n, void *aux, cmp_fun_t cmp) {
  stable_sorter_t sorter;

  init_stable_sorter(&sorter, aux, cmp);
  apply_sorter(&sorter, a, n);
  delete_stable_sorter(&sorter);
}


