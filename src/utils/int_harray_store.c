/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <assert.h>

#include "utils/int_array_sort.h"
#include "utils/int_harray_store.h"
#include "utils/ptr_array_sort.h"

/*
 * Initialize: use default sizes for all components
 */
void init_harray_store(int_harray_store_t *store) {
  init_int_array_hset(&store->hset, 0);
  init_ivector(&store->buffer, 0);
  init_int_hset(&store->aux, 0);
}

/*
 * Delete: free memory
 */
void delete_harray_store(int_harray_store_t *store) {
  delete_int_array_hset(&store->hset);
  delete_ivector(&store->buffer);
  delete_int_hset(&store->aux);
}

/*
 * Reset: remove all elements from hset
 */
void reset_harray_store(int_harray_store_t *store) {
  reset_int_array_hset(&store->hset);
  ivector_reset(&store->buffer);
  int_hset_reset(&store->aux);
}



/*
 * For debugging: check that a is sorted and does not contain duplicates
 */
#ifndef NDEBUG
static bool good_set(harray_t *a) {
  uint32_t i, n;
  int32_t x;

  n = a->nelems;
  if (n > 1) {
    x = a->data[0];
    for (i = 1; i<n; i++) {
      if (a->data[i] <= x) return false; // not sorted or duplicate
      x = a->data[i];
    }
  }

  return true;
}

#endif

/*
 * Construct the set that contains elements x[0]  ... x[n-1]
 * - this sorts array x and removes duplicates then constructs the harray
 * - x may be modified.
 */
harray_t *make_harray(int_harray_store_t *store, uint32_t n, int32_t *x) {
  harray_t *a;
  uint32_t i, j;
  int32_t y;

  if (n == 0) {
    a = empty_harray(store);
  } else {
    int_array_sort(x, n);
    // remove duplicates from x[0 .. n-1]
    y = x[0];
    j = 1;
    for (i=1; i<n; i++) {
      assert(y <= x[i]);
      if (x[i] != y) {
	x[j] = x[i];
	y = x[i];
	j ++;
      }
    }
    a = int_array_hset_get(&store->hset, j, x);
    assert(good_set(a));
  }

  return a;
}


/*
 * Add all elements of a to vector v and to hset
 * - skip elements that are already in hset
 */
static void harray_merge(ivector_t *v, int_hset_t *hset, const harray_t *a) {
  uint32_t i, n;
  int32_t x;

  n = a->nelems;
  for (i=0; i<n; i++) {
    x = a->data[i];
    if (int_hset_add(hset, x)) { // new element
      ivector_push(v, x);
    }
  }
}


/*
 * Construct the union of two sets
 * - a and b must be form the store
 */
harray_t *merge_two_harrays(int_harray_store_t *store, harray_t *a, harray_t *b) {
  ivector_t *v;
  int_hset_t *aux;

  if (a != b) {
    v = &store->buffer;
    aux = &store->aux;
    assert(v->size == 0 && int_hset_is_empty(aux));

    harray_merge(v, aux, a);
    harray_merge(v, aux, b);
    int_array_sort(v->data, v->size);
    a = int_array_hset_get(&store->hset, v->size, v->data);
    assert(good_set(a));

    ivector_reset(v);
    int_hset_reset(aux);
  }

  return a;
}

/*
 * Construct the union of n sets a[0 ... n-1]
 * - a may be modified
 * - return the empty set if n is zero
 */
harray_t *merge_harrays(int_harray_store_t *store, harray_t **a, uint32_t n) {
  harray_t *b, *c;
  ivector_t *v;
  int_hset_t *aux;
  uint32_t i;
  
  if (n == 0) {
    b = empty_harray(store);
  } else if (n == 1) {
    b = a[0];
  } else if (n == 2) {
    b = merge_two_harrays(store, a[0], a[1]);
  } else {
    v = &store->buffer;
    aux = &store->aux;
    assert(v->size == 0 && int_hset_is_empty(aux));

    /*
     * Store all elements of a[0] ... a[n-1] in v
     */
    ptr_array_sort((void **) a, n);
    b = a[0];
    for (i=1; i<n; i++) {
      c = a[i];
      if (c != b) {
        harray_merge(v, aux, b);
        b = c;
      }
    }

    /*
     * b is a[i], for some i and elements of b have not been
     * processed yet. If i = 0, then all elements of a are
     * equal to b so the result is b.
     */
    if (b != a[0]) {
      harray_merge(v, aux, b);

      assert(v->size > 0 && int_hset_is_nonempty(aux));
      int_array_sort(v->data, v->size);
      b = int_array_hset_get(&store->hset, v->size, v->data);
      assert(good_set(b));

      ivector_reset(v);
      int_hset_reset(aux);
    }
  }

  return b;
}


/*
 * Return a - { x[0] .... x[n-1] }
 */
harray_t *harray_remove_elem(int_harray_store_t *store, harray_t *a, uint32_t n, int32_t *x) {
    ivector_t *v;
  int_hset_t *aux;
  uint32_t i;
  int32_t y;

  v = &store->buffer;
  aux = &store->aux;
  assert(v->size == 0 && int_hset_is_empty(aux));

  // store x[0] ... x[n-1] in aux
  for (i=0; i<n; i++) {
    (void) int_hset_add(aux, x[i]);
  }

  /*
   * store elements of a - aux into v.
   * the elements are sorted in v.
   */
  n = a->nelems;
  for (i=0; i<n; i++) {
    y = a->data[i];
    if (! int_hset_member(aux, y)) {
      ivector_push(v, y);
    }
  }
  a = int_array_hset_get(&store->hset, v->size, v->data);
  assert(good_set(a));

  ivector_reset(v);
  int_hset_reset(aux);

  return a;
}

