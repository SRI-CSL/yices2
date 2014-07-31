/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <inttypes.h>

#include "context/eq_abstraction.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}
#endif


/*
 * Global manager
 */
static epartition_manager_t mngr;

/*
 * Array of partitions
 */
#define NUM_PARTITIONS  200

static epartition_t *partition[NUM_PARTITIONS];

/*
 * Test partitions
 */
static term_t test1[10] = {
  1, 2, 3, NULL_TERM,
  4, 5, 6, 7, 8, NULL_TERM,
};

static term_t test2[11] = {
  5, 9, 6, NULL_TERM,
  3, 1, NULL_TERM,
  2, 8, 4, NULL_TERM,
};

static term_t test3[15] = {
  1, 4, 6, 3, NULL_TERM,
  10, 11, 5, NULL_TERM,
  7, 8, NULL_TERM,
  9, 2, NULL_TERM,
};



/*
 * Print partition p
 */
static void print_partition(epartition_t *p) {
  term_t *q, t;
  uint32_t i, n;

  n = p->nclasses;
  q = p->data;
  for (i=0; i<n; i++) {
    printf(" {");
    t = *q ++;
    while (t >= 0) {
      printf(" %"PRId32, t);
      t = *q ++;
    }
    printf(" }");
  }
  printf("\n");
}


/*
 * Print manager content
 */
static void print_manager(void) {
  uint32_t i, n;
  term_t r, t;

  printf("emanager: %p\n", &mngr);
  printf("  e_size = %"PRIu32"\n", mngr.e_size);
  printf("  c_size = %"PRIu32"\n", mngr.c_size);
  printf("  sc_size = %"PRIu32"\n", mngr.sc_size);
  printf("  nterms = %"PRIu32"\n", mngr.nterms);
  printf("  nclasses = %"PRIu32"\n", mngr.nclasses);
  printf("  order = %"PRIu32"\n", mngr.order);

  n = mngr.nclasses;
  for (i=0; i<n; i++) {
    printf("  class %"PRIu32":", i);
    r = mngr.root[i];
    if (r < 0) {
      printf(" removed\n");
    } else {
      t = r;
      do {
	printf(" %"PRId32, t);
	t = mngr.next[t];
      } while (t != r);
      printf("\n");
    }
  }

  n = mngr.e_size;
  for (i=0; i<n; i++) {
    if (mngr.label[i] >= 0) {
      printf("  label[%"PRIu32"] = %"PRId32"\n", i, mngr.label[i]);
    }
  }
}





/*
 * Generate a random binary partition
 */
static epartition_t *random_partition(uint32_t scale) {
  int32_t x, y;

  assert(scale >= 2);
  x = random() % scale;
  do {
    y = random() % scale;
  } while (y == x);

  return basic_epartition(x, y);
}



/*
 * Generate n random partitions and store them in the global array
 */
static void build_random_partitions(uint32_t n, uint32_t scale) {
  uint32_t i;

  assert(n <= NUM_PARTITIONS);

  for (i=0; i<n; i++) {
    partition[i] = random_partition(scale);
  }
}


/*
 * Make a partition object from array a:
 * - a[0] ... a[n-1] store the classes, separated by NULL_ETERM
 * - the last element a[n-1] must be NULL_ETERM
 */
static epartition_t *make_epartition(term_t *a, uint32_t n) {
  epartition_t *tmp;
  uint32_t i;

  tmp = (epartition_t *) safe_malloc(sizeof(epartition_t) + n * sizeof(int32_t));
  tmp->nclasses = 0;
  tmp->size = n;
  for (i=0; i<n; i++) {
    tmp->data[i] = a[i];
    if (a[i] == NULL_TERM) {
      tmp->nclasses ++;
    }
  }

  return tmp;
}



/*
 * Delete all partitions in the global array
 * - n = number of partitions allocated
 */
static void delete_partitions(uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    delete_epartition(&mngr, partition[i]);
    partition[i] = NULL;
  }
}



/*
 * Contruct meet p[0] ... p[n-1]
 */
static epartition_t *test_meet(epartition_t **p, uint32_t n) {
  uint32_t i;
  epartition_t *p0;

  printf("--- Test meet ---\n");
  for (i=0; i<n; i++) {
    printf("p[%"PRId32"] = ", i);
    print_partition(p[i]);
  }

  if (n == 0) {
    p0 = empty_epartition(&mngr);
  } else {
    epartition_init_for_meet(&mngr, p[0]);
    for (i=1; i<n; i++) {
      epartition_meet(&mngr, p[i]);
    }
    p0 = epartition_get_meet(&mngr);
  }

  printf("Result: ");
  print_partition(p0);
  printf("------\n");

  return p0;
}


/*
 * Test meet on random partitions
 */
static void test_meets(void) {
  uint32_t n, m;
  epartition_t *p;

  for (n=0; n<100; n++) {
    m = random() % 30;
    build_random_partitions(m, 30);
    p = test_meet(partition, m);
    delete_partitions(m);
    delete_epartition(&mngr, p);
  }

  printf("\n\n\n\n");

#if 0
  build_random_partitions(100, 250);
  for (n=100; n<NUM_PARTITIONS; n++) {
    p = test_meet(partition, n);
    partition[n] = p;
  }
  delete_partitions(NUM_PARTITIONS);
#endif
}




/*
 * Contruct join p[0] ... p[n-1]
 */
static epartition_t *test_join(epartition_t **p, uint32_t n) {
  uint32_t i;
  epartition_t *p0;

  printf("--- Test join ---\n");
  for (i=0; i<n; i++) {
    printf("p[%"PRId32"] = ", i);
    print_partition(p[i]);
  }

  if (n == 0) {
    p0 = empty_epartition(&mngr);
  } else {
    epartition_init_for_join(&mngr, p[0]);
    for (i=1; i<n; i++) {
      epartition_join(&mngr, p[i]);
    }
    p0 = epartition_get_join(&mngr);
  }

  printf("Result: ");
  print_partition(p0);
  printf("------\n");

  return p0;
}


/*
 * Test join on random partitions
 */
static void test_joins(void) {
  uint32_t i, n, m;
  epartition_t *p;

  for (n=0; n<100; n++) {
    m = random() % 10;
    build_random_partitions(m, 30);
    for (i=1; i<m; i++) {
      p = test_join(partition, i);
      delete_epartition(&mngr, p);
    }
    delete_partitions(m);
  }

  partition[0] = make_epartition(test1, 10);
  partition[1] = make_epartition(test1, 10);
  partition[2] = test_join(partition, 2);
  delete_partitions(3);

  partition[0] = make_epartition(test1, 10);
  partition[1] = make_epartition(test2, 11);
  partition[2] = test_join(partition, 2);
  delete_partitions(3);

  partition[0] = make_epartition(test1, 10);
  partition[1] = make_epartition(test3, 15);
  partition[2] = test_join(partition, 2);
  delete_partitions(3);

  partition[0] = make_epartition(test2, 11);
  partition[1] = make_epartition(test1, 10);
  partition[2] = test_join(partition, 2);
  delete_partitions(3);

  partition[0] = make_epartition(test2, 11);
  partition[1] = make_epartition(test2, 11);
  partition[2] = test_join(partition, 2);
  delete_partitions(3);

  partition[0] = make_epartition(test2, 11);
  partition[1] = make_epartition(test3, 15);
  partition[2] = test_join(partition, 2);
  delete_partitions(3);


  partition[0] = make_epartition(test1, 10);
  partition[1] = make_epartition(test2, 11);
  partition[2] = make_epartition(test3, 15);
  partition[3] = test_join(partition, 3);
  delete_partitions(4);

  partition[0] = make_epartition(test2, 11);
  partition[1] = make_epartition(test1, 10);
  partition[2] = make_epartition(test2, 11);
  partition[3] = test_join(partition, 3);
  delete_partitions(4);

  partition[0] = make_epartition(test2, 11);
  partition[1] = make_epartition(test3, 15);
  partition[2] = make_epartition(test3, 15);
  partition[3] = test_join(partition, 3);
  delete_partitions(4);

  partition[0] = make_epartition(test3, 15);
  partition[1] = make_epartition(test3, 15);
  partition[2] = make_epartition(test3, 15);
  partition[3] = test_join(partition, 3);
  delete_partitions(4);
}


int main() {
  init_epartition_manager(&mngr);
  printf("--- Init ---\n");
  print_manager();
  printf("\n");

  test_meets();
  printf("\n--- After meet ---\n");
  print_manager();
  printf("\n");

  test_joins();
  printf("\n--- After join ---\n");
  print_manager();
  printf("\n");

  delete_epartition_manager(&mngr);

  return 0;
}
