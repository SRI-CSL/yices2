/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/bitvectors.h"
#include "model/rb_bvsets.h"

#ifdef MINGW

static inline long int random(void) {
  return rand();
}

#endif


/*
 * Print subtree of root i
 */
static void recur_print_tree(rbtree_t *tree, uint32_t i) {
  if (i > 0) {
    recur_print_tree(tree, rbtree_node_left_child(tree, i));
    printf(" %"PRIu32, rbtree_node_value(tree, i));
    recur_print_tree(tree, rbtree_node_right_child(tree, i));
  }
}


/*
 * Print the content of set s
 */
static void print_bvset(rb_bvset_t *s) {
  printf("set %p\n", s);
  printf("  max_val = %"PRIu32"\n", s->max_val);
  printf("  ptr = %"PRIu32"\n", s->ptr);
  printf("  content:");
  recur_print_tree(&s->tree, s->tree.root);
  printf("\n");
}


/*
 * Add n random elements to set s
 * - mask = 2^k - 1 where k = bitsize considered
 *   (i.e., elements are in the interval [0, 2^k-1]
 */
static void add_random(rb_bvset_t *s, uint32_t n, uint32_t mask) {
  uint32_t i, x;

  for (i=0; i<n; i++) {
    x = ((uint32_t) random()) & mask;
    rb_bvset_add(s, x);
  }
}


/*
 * Initialization:
 * - n = bit size
 * - add m random elements
 */
static void init_test_set(rb_bvset_t *s, uint32_t n, uint32_t m) {
  uint32_t mask;

  init_rb_bvset(s, n);
  if (n < 32) {
    mask = (1<<n) - 1;
  } else {
    mask = UINT32_MAX;
  }
  add_random(s, m, mask);
}


/*
 * Global set
 */
static rb_bvset_t set;



/*
 * First test: size = 64
 */
static void test1(void) {
  uint32_t x;

  printf("\n"
	 "=================\n"
	 "     TEST 1\n"
	 "=================\n\n");

  // 50 initial elements
  init_test_set(&set, 6, 50);
  printf("=== Initial set: 50 additions ===\n");
  print_bvset(&set);
  printf("\n");

  while (! rb_bvset_full(&set)) {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  reset_rb_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  // 40 initial elements
  add_random(&set, 40, 63);
  printf("\n=== After 40 additions ===\n");
  print_bvset(&set);
  printf("\n");

  while (! rb_bvset_full(&set)) {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");


  // empty initial set
  reset_rb_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  while (! rb_bvset_full(&set)) {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_rb_bvset(&set);
}



/*
 * Second test: size = 256
 */
static void test2(void) {
  uint32_t x;

  printf("\n"
	 "=================\n"
	 "     TEST 2\n"
	 "=================\n\n");

  // 200 initial additions
  init_test_set(&set, 8, 200);
  printf("=== Initial set: 200 additions ===\n");
  print_bvset(&set);
  printf("\n");

  while (! rb_bvset_full(&set)) {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  reset_rb_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  // 240 initial elements
  add_random(&set, 240, 255);
  printf("\n=== After 240 additions ===\n");
  print_bvset(&set);
  printf("\n");

  while (! rb_bvset_full(&set)) {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");


  // empty initial set
  reset_rb_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  while (! rb_bvset_full(&set)) {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_rb_bvset(&set);
}



/*
 * Size = 2^40
 */
static void test3(void) {
  uint32_t x, n;

  printf("\n"
	 "=================\n"
	 "     TEST 3\n"
	 "=================\n\n");

  // 1000 initial additions
  init_test_set(&set, 40, 1000);
  printf("=== Initial set: 1000 additions ===\n");
  print_bvset(&set);
  printf("\n");

  // 50 calls to get_fresh
  n = 50;
  do {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
    n --;
  } while (n > 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  reset_rb_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  // 2000 initial additions
  add_random(&set, 2000, UINT32_MAX);
  printf("\n=== After 2000 additions ===\n");
  print_bvset(&set);
  printf("\n");

  // 2000000 calls to get fresh
  n = 2000000;
  do {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
    n --;
  } while (n > 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");


  // empty initial set
  reset_rb_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  // 200000 calls to get fresh
  n = 200000;
  do {
    x = rb_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, rbtree_card(&set.tree));
    n --;
  } while (n > 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_rb_bvset(&set);
}





/*
 * Main test
 */
int main() {
  test1();
  test2();
  test3();

  return 0;
}
