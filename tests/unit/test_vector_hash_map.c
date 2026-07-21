/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/vector_hash_map.h"

static void show_vector(FILE *f, vhmap_vector_t *v) {
  uint32_t i, n;

  fprintf(f, "key %"PRId32": ", v->key);
  n = v->nelems;
  if (n == 0) {
    fprintf(f, "[]");
  } else {
    fprintf(f, "[%"PRId32, v->data[0]);
    for (i=1; i<n; i++) {
      fprintf(f, " %"PRId32, v->data[i]);
    }
    fprintf(f, "]");
  }
}

static void show_hmap(FILE *f, vector_hmap_t *hmap) {
  vhmap_vector_t *v;
  uint32_t i, n;
  
  fprintf(f, "hash-map %p\n", hmap);
  fprintf(f, "  size = %"PRIu32"\n", hmap->size);
  fprintf(f, "  nelems = %"PRIu32"\n", hmap->nelems);
  fprintf(f, "  resize threshold = %"PRIu32"\n", hmap->resize_threshold);
  fprintf(f, "  content:\n");

  n = hmap->size;
  for (i=0; i<n; i++) {
    v = hmap->data[i];
    if (v != NULL) {
      fprintf(f, "    ");
      show_vector(f, v);
      fprintf(f, "\n");
    }
  }
  fprintf(f, "----\n");
}



/*
 * For testing: add x to all vectors of key k such that k divides x
 */
static void add_element(vector_hmap_t *hmap, int32_t x) {
  int32_t k;

  assert(x > 0);

  for (k=1; k <= x; k++) {
    if (x % k == 0) {
      vector_hmap_add(hmap, k, x);
    }
  }
}

/*
 * Number of multiples of k in the interval [1 ... 23]
 */
static uint32_t multiples(int32_t k) {
  int32_t x;
  uint32_t c;

  assert(k > 0);

  c = 0;
  for (x=1; x<=23; x++) {
    if (x % k == 0) {
      c ++;
    }
  }
  return c;
}


/*
 * Check that vector of key k contains all integers in [1 ... 23] that
 * are multiple of k
 */
static void check_vector(const vector_hmap_t *hmap, int32_t k) {
  vhmap_vector_t *v;
  uint32_t i, n, c;
  int32_t x;

  v = vector_hmap_find(hmap, k);
  if (k < 1 || k > 23) {
    // no vector with that key
    if (v != NULL) {
      fprintf(stderr, "*** BUG: found vector %p of key %"PRId32" ***\n", v, k);
      fprintf(stderr, "    expected NULL\n");
      exit(1);
    }
  } else {

    if (v->key != k) {
      fprintf(stderr, "*** BUG: bad vector for key %"PRId32" (v->key = %"PRId32") ***\n", k, v->key);
      exit(1);
    }

    n = v->nelems;
    for (i=0; i<n; i++) {
      x = v->data[i];
      if (x < 1 || x > 23) {
	fprintf(stderr, "*** BUG: out-of-range element in vector key %"PRId32" (x = %"PRId32") ***\n", k, x);
	exit(1);
      }
      if (x % k != 0) {
	fprintf(stderr, "*** BUG: bad element in vector of key %"PRId32" (x = %"PRId32") ***\n", k, x);
	exit(1);
      }
    }

    c = multiples(k);
    if (n < c) {
      fprintf(stderr,
	      "*** BUG: missing elements in vector of key %"PRId32" (expected %"PRIu32", got %"PRIu32") ***\n",
	      k, c, n);
      exit(1);
    }
    if (n > c) {
      fprintf(stderr,
	      "*** BUG: too many elements in vector of key %"PRId32" (expected %"PRIu32", got %"PRIu32") ***\n",
	      k, c, n);
      exit(1);
    }
  }

  printf("Vector of key %"PRId32" looks correct\n", k);
}

static vector_hmap_t hmap;


int main(void) {
  int32_t x;
  
  init_vector_hmap(&hmap, 8);
  printf("--- After initialization ---\n");
  show_hmap(stdout, &hmap);

  for (x=1; x <= 23; x++) {
    add_element(&hmap, x);
  }

  printf("--- After additions ---\n");
  show_hmap(stdout, &hmap);

  for (x=-1; x <= 25; x++) {
    check_vector(&hmap, x);
  }

  reset_vector_hmap(&hmap);
  printf("--- After reset ---\n");
  show_hmap(stdout, &hmap);
  
  delete_vector_hmap(&hmap);
  
  return 0;
}
