/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "utils/memalloc.h"
#include "utils/union_find.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}
#endif


static partition_t partition;


/*
 * Print the union-find data
 */
static void print_partition_details(partition_t *p) {
  int32_t x;

  printf("partition %p\n", p);
  printf("  size = %"PRIu32"\n", p->size);
  printf("  nelems = %"PRIu32"\n", p->nelems);
  if (p->nelems > 0) {
    printf("  content\n");
    for (x=0; x<p->nelems; x++) {
      if (p->parent[x] >= 0) {
	printf("    item: %"PRId32", parent = %"PRId32", rank = %"PRIu32"\n",
	       x, p->parent[x], (uint32_t) p->rank[x]);
      }
    }
  }
}

/*
 * Print each class
 */
static void print_partition(partition_t *p) {
  int32_t i, j, n;
  int32_t x, *aux;

  n = p->nelems;
  aux = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    aux[i] = partition_find(p, i);
  }

  for (i=0; i<n; i++) {
    x = aux[i];
    if (x >= 0) {
      printf("class[%2"PRId32"]: %2"PRId32, x, i);
      aux[i] = -1;
      for (j=i+1; j<n; j++) {
	if (aux[j] == x) {
	  printf(" %2"PRId32, j);
	  aux[j] = -1;
	}
      }
      printf("\n");
    }
  }

  safe_free(aux);
}


#define N 20

static int32_t aux[N];


int main(void) {
  uint32_t i;
  int32_t x, y, rx, ry;

  init_partition(&partition, 0);
  printf("\n*** Initial partition ***\n");
  print_partition_details(&partition);

  for (i=0; i<40; i++) {
    x = random() % N;
    printf("--- testing %"PRId32" ---\n", x);
    y = partition_find(&partition, x);
    if (y < 0) {
      printf("item %"PRId32" not present; adding it\n", x);
      partition_add(&partition, x);
    } else {
      printf("root[%"PRId32"] = %"PRId32"\n", x, y);
    }
  }

  printf("\n*** Partition ***\n");
  print_partition_details(&partition);
  printf("\n");

  print_partition(&partition);
  printf("\n");

  for (x=0; x<N; x++) {
    aux[x] = partition_find(&partition, x);
  }
  for (i=1; i<10; i++) {
    do { x = random() % N; } while (aux[x] < 0);
    do { y = random() % N; } while (x == y || aux[y] < 0);

    x = partition_find(&partition, x);
    y = partition_find(&partition, y);
    if (x != y) {
      printf("--- Merging %"PRId32" and %"PRId32" ---\n", x, y);
      partition_merge(&partition, x, y);
    }
  }
  printf("\n");
  print_partition(&partition);

  reset_partition(&partition);

  for (i=0; i<100; i++) {
    x = random() % 300;
    rx = partition_find(&partition, x);
    if (rx < 0) {
      partition_add(&partition, x);
      rx = x;
    }
    y = random() % 300;
    ry = partition_find(&partition, y);
    if (ry < 0) {
      partition_add(&partition, y);
      ry = y;
    }
    if (rx != ry) {
      partition_merge(&partition, rx, ry);
    }
  }

  printf("\n\n");
  print_partition(&partition);

  delete_partition(&partition);

  return 0;
}
