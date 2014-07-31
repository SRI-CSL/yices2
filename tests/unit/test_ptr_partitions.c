/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/hash_functions.h"
#include "utils/ptr_partitions.h"



/*
 * Objects: pairs of integers
 */
typedef struct pair_s {
  int32_t left;
  int32_t right;
} pair_t;


/*
 * Hash code for a pair (x, y)
 */
static uint32_t hash(void *aux, pair_t *p) {
  return jenkins_hash_pair(p->left, p->right, 0x283a8d2a);
}


/*
 * Equality test
 */
static bool match(void *aux, pair_t *p1, pair_t *p2) {
  return p1->left == p2->left && p1->right == p2->right;
}


/*
 * Array of pairs used for testing
 */
#define NOBJ 100

static pair_t testobj[NOBJ];


/*
 * Initialization of testobj
 */
static void init_testobj(void) {
  uint32_t i;

  for (i=0; i<NOBJ; i++) {
    testobj[i].left = i % 8;
    testobj[i].right = i % 6;
  }
}


/*
 * Change them
 */
static void init_testobj2(void) {
  uint32_t i;

  for (i=0; i<NOBJ; i++) {
    testobj[i].left = i % 5;
    testobj[i].right = i % 13;
  }
}


/*
 * Print record r
 */
static void print_ppart_record(ppart_rec_t *r) {
  printf("[hash = %08"PRIx32", cid = %"PRId32", data = %p]", r->hash, r->cid, r->data);
}


/*
 * Print vector v
 */
static void print_ppart_vector(void **v) {
  uint32_t i, n;

  n = ppv_size(v);
  for (i=0; i<n; i++) {
    printf(" (%"PRId32" %"PRId32")", ((pair_t*) v[i])->left, ((pair_t *) v[i])->right);
  }
}


/*
 * Print hash table + classes
 */
static void print_ppart(ppart_t *pp) {
  ppart_rec_t *d;
  uint32_t i, n;

  printf("pp %p\n", pp);
  printf("  size = %"PRIu32"\n", pp->size);
  printf("  nelems = %"PRIu32"\n", pp->nelems);
  printf("  csize = %"PRIu32"\n", pp->csize);
  printf("  nclasses = %"PRIu32"\n", pp->nclasses);

  n = pp->nelems;
  if (n > 0) {
    printf("  Content\n");
    d = pp->records;
    n = pp->size;
    for (i=0; i<n; i++) {
      if (d->data != NULL) {
	printf("   rec[%"PRIu32"]: ", i);
	print_ppart_record(d);
	printf("\n");
      }
      d ++;
    }
  }

  n = pp->nclasses;
  if (n > 0) {
    printf("  Classes\n");
    for (i=0; i<n; i++) {
      printf("   class[%"PRIu32"]: ", i);
      print_ppart_vector(pp->classes[i]);
      printf("\n");
    }
  }
}




/*
 * Global partition table
 */
static ppart_t pp;



int main(void) {
  uint32_t i;

  init_testobj();
  init_ptr_partition(&pp, 16, NULL, (ppart_hash_fun_t) hash, (ppart_match_fun_t) match);
  printf("=== Init ===\n");
  print_ppart(&pp);
  printf("\n\n");

  for (i=0; i<NOBJ; i++) {
    ptr_partition_add(&pp, testobj + i);
    if (i % 10 == 9) {
      printf("=== Added %"PRIu32" objects ===\n", i+1);
      print_ppart(&pp);
      printf("\n\n");
    }
  }

  printf("=== Final ===\n");
  print_ppart(&pp);
  printf("\n\n");



  reset_ptr_partition(&pp);
  printf("=== After reset ===\n");
  print_ppart(&pp);
  printf("\n\n");

  init_testobj2();
  for (i=0; i<NOBJ; i++) {
    ptr_partition_add(&pp, testobj + i);
    if (i % 10 == 9) {
      printf("=== Added %"PRIu32" objects ===\n", i+1);
      print_ppart(&pp);
      printf("\n\n");
    }
  }

  printf("=== Final ===\n");
  print_ppart(&pp);
  printf("\n\n");

  delete_ptr_partition(&pp);

  return 0;
}
