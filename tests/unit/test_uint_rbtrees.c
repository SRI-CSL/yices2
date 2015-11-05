/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/uint_rbtrees.h"

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
 * Print content of tree
 */
static void print_tree(rbtree_t *tree) {
  printf("Tree %p\n", tree);
  printf("  size = %"PRIu32"\n", tree->size);
  printf("  num nodes = %"PRIu32"\n", tree->nbnodes);
  printf("  root = %"PRIu32"\n", tree->root);
  printf("  content: ");
  recur_print_tree(tree, tree->root);
  printf("\n");
}


/*
 * Print more details
 */
static void print_all_nodes(rbtree_t *tree) {
  uint32_t i, n;

  printf("  nodes\n");
  n = tree->nbnodes;
  for (i=1; i<n; i++) {
    printf("   node[%"PRIu32"]: val = %"PRIu32", left = %"PRIu32", right = %"PRIu32,
	   i, rbtree_node_value(tree, i), rbtree_node_left_child(tree, i),
	   rbtree_node_right_child(tree, i));
    if (tst_bit(tree->isred, i)) {
      printf(", red\n");
    } else {
      printf(", black\n");
    }
  }
  printf("  root = %"PRId32"\n\n", tree->root);
}


/*
 * Global tree used for testing + test data
 */
#define SMALL_SIZE 100
#define NDATA 1000000

static rbtree_t tree;
static uint32_t data[NDATA];


/*
 * Initialize data a with n random values in the interval [0 .. 99]
 */
static void random_data(uint32_t *a, uint32_t n) {
  uint32_t i, d;

  d = 4 * n;
  for (i=0; i<n; i++) {
    a[i] = ((uint32_t) random()) % d;
  }
}


/*
 * Initialize data with n increasing values
 */
static void random_increasing(uint32_t *a, uint32_t n) {
  uint32_t i, x;

  x = 0;
  for (i=0; i<n; i++) {
    x += ((uint32_t) random()) % 4;
    a[i] = x;
  }
}


/*
 * Initiallize data with n decreasing values
 */
static void random_decreasing(uint32_t *a, uint32_t n) {
  uint32_t x;

  x = 0;
  while (n > 0) {
    n --;
    x += ((uint32_t) random()) % 4;
    a[n] = x;
  }
}


/*
 * Test tree using data from a. n = size of array a
 * - tree must be initialized
 */
static void test_tree(rbtree_t *tree, uint32_t *a, uint32_t n) {
  uint32_t i, x;
  uint32_t j, k;
  bool new;

  for (i=0; i<n; i++) {
    x = a[i];
    j = rbtree_find(tree, x);
    k = rbtree_get(tree, x, &new);
    assert(rbtree_node_value(tree, k) == x);
    if (j == null_rbnode) {
      printf("--> adding %"PRIu32" at node %"PRIu32"\n", x, k);
      assert(new);
    } else {
      printf("--> found %"PRIu32" at node %"PRIu32"\n", x, j);
      assert(!new && k == j);
    }
  }

  printf("--- Final set ---\n");
  print_tree(tree);
  print_all_nodes(tree);
  printf("\n");
}



/*
 * Test of the scanning function
 */
static void test_scan_tree(rbtree_t *tree) {
  uint32_t i, x, y;

  printf("--- Test scan ---\n");
  x = 0;
  for (;;) {
    i = rbtree_find_sup(tree, x);
    if (i == 0) {
      printf("sup(%"PRIu32"): node %"PRIu32" (no element)\n", x, i);
      break;
    } else {
      y = rbtree_node_value(tree, i);
      assert(x <= y);
      printf("sup(%"PRIu32"): node %"PRIu32", val = %"PRIu32"\n", x, i, y);
      if (y == UINT32_MAX) break;
      x = y+1;
    }
  }
  printf("\n");
}


/*
 * Speed test: add all elements of a into tree.
 */
static void test_tree_speed_add(rbtree_t *tree, uint32_t *a, uint32_t n) {
  uint32_t i, x;
  uint32_t cnt; // number of additions
  bool new;

  cnt = 0;
  for (i=0; i<n; i++) {
    x = a[i];
    (void) rbtree_get(tree, x, &new);
    if (new) {
      cnt ++;
    }
  }
  printf("Add test:    size = %"PRIu32", added = %"PRIu32"\n", n, cnt);
}

/*
 * Speed test: search all elements of a
 */
static void test_tree_speed_find(rbtree_t *tree, uint32_t *a, uint32_t n) {
  uint32_t i, x, k;
  uint32_t cnt; // number of elements found

  cnt = 0;
  for (i=0; i<n; i++) {
    x = a[i];
    k = rbtree_find(tree, x);
    if (k > 0) {
      cnt ++;
    }
  }
  printf("Search test: size = %"PRIu32", found = %"PRIu32"\n", n, cnt);
}

/*
 * Repeat speed test 100 times
 */
static void repeat_test_speed(rbtree_t *tree) {
  uint32_t i;

  printf("RANDOM INPUT\n");
  for (i=0; i<60; i++) {
    random_data(data, NDATA);
    test_tree_speed_add(tree, data, NDATA);
    test_tree_speed_find(tree, data, NDATA);
    random_data(data, NDATA);
    test_tree_speed_find(tree, data, NDATA);
    reset_rbtree(tree);
  }

  printf("INCREASINNG INPUT\n");
  for (i=0; i<20; i++) {
    random_increasing(data, NDATA);
    test_tree_speed_add(tree, data, NDATA);
    test_tree_speed_find(tree, data, NDATA);
    random_data(data, NDATA);
    test_tree_speed_find(tree, data, NDATA);
    reset_rbtree(tree);
  }

  printf("DECREASINNG INPUT\n");
  for (i=0; i<20; i++) {
    random_decreasing(data, NDATA);
    test_tree_speed_add(tree, data, NDATA);
    test_tree_speed_find(tree, data, NDATA);
    random_data(data, NDATA);
    test_tree_speed_find(tree, data, NDATA);
    reset_rbtree(tree);
  }
}


#if 0
// NOT USED ANYMORE

/*
 * Test rotations
 */
extern void test_rotate(rbtree_t *tree, uint32_t p, uint32_t q, uint32_t r);

// random child of node r
static uint32_t random_child(rbtree_t *tree, uint32_t r) {
  uint32_t k;

  assert(r != null_rbnode && r < tree->nbnodes);

  if (random() & 0x08) {
    k = rbtree_node_right_child(tree, r);
  } else {
    k = rbtree_node_left_child(tree, r);
  }
  return k;
}

static void test_rotations(rbtree_t *tree) {
  uint32_t p, q, r, n, i;

  n = rbtree_num_nodes(tree);
  for (i=0; i<400; i++) {
    r = ((uint32_t) random()) % n;

    if (r == null_rbnode) {
      q = tree->root;
    } else {
      q = random_child(tree, r);
    }

    if (q != null_rbnode) {
      p = random_child(tree, q);

      if (p != null_rbnode) {
	test_rotate(tree, p, q, r);

	printf("--- After rotation of %"PRIu32" and %"PRIu32" ---\n", p, q);
	print_tree(tree);
	//	print_all_nodes(tree);
	printf("\n");
      }
    }
  }

}

#endif

/*
 * Run tests
 */
int main(void) {
  init_rbtree(&tree, 10); // use small size to trigger resizing

  printf("--- After init ---\n");
  print_tree(&tree);
  printf("\n");
  test_scan_tree(&tree);

  printf("--- Random test ---\n");
  random_data(data, SMALL_SIZE);
  test_tree(&tree, data, SMALL_SIZE);
  test_scan_tree(&tree);

  reset_rbtree(&tree);
  printf("--- After reset ---\n");
  print_tree(&tree);
  printf("\n");


  printf("--- Random test ---\n");
  random_data(data, SMALL_SIZE);
  test_tree(&tree, data, SMALL_SIZE);
  test_scan_tree(&tree);

  reset_rbtree(&tree);
  printf("--- After reset ---\n");
  print_tree(&tree);
  printf("\n");


  printf("--- Increasing test ---\n");
  random_increasing(data, SMALL_SIZE);
  test_tree(&tree, data, SMALL_SIZE);
  test_scan_tree(&tree);

  reset_rbtree(&tree);
  printf("--- After reset ---\n");
  print_tree(&tree);
  printf("\n");


  printf("--- Increasing test ---\n");
  random_increasing(data, SMALL_SIZE);
  test_tree(&tree, data, SMALL_SIZE);
  test_scan_tree(&tree);

  reset_rbtree(&tree);
  printf("--- After reset ---\n");
  print_tree(&tree);
  printf("\n");


  printf("--- Decreasing test ---\n");
  random_decreasing(data, SMALL_SIZE);
  test_tree(&tree, data, SMALL_SIZE);
  test_scan_tree(&tree);

  reset_rbtree(&tree);
  printf("--- After reset ---\n");
  print_tree(&tree);
  printf("\n");


  printf("--- Decreasing test ---\n");
  random_decreasing(data, SMALL_SIZE);
  test_tree(&tree, data, SMALL_SIZE);
  test_scan_tree(&tree);

  reset_rbtree(&tree);
  printf("--- After reset ---\n");
  print_tree(&tree);
  printf("\n");

  printf("\n\n**** SPEED TEST ****\n\n");
  repeat_test_speed(&tree);

  delete_rbtree(&tree);

  return 0;
}
