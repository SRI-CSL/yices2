/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>
#include <assert.h>
#include <stdlib.h>

#include "terms/rationals.h"
#include "terms/pprod_table.h"
#include "terms/balanced_arith_buffers.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Check ordering
 */

// check whether the subtree rooted at x is ordered
static bool is_ordered(rba_buffer_t *b, uint32_t x) {
  uint32_t i, j;
  pprod_t *r, *s, *t;

  assert(x < b->num_nodes);

  if (x == 0) return true;

  i = b->child[x][0];  // left child
  j = b->child[x][1];  // right child
  r = b->mono[x].prod;
  s = b->mono[i].prod;
  t = b->mono[j].prod;

  // the expected order is s < r < t
  if (i != 0 && !pprod_precedes(s, r)) {
    printf("tree not ordered at node %"PRIu32" (for left child %"PRIu32")\n", x, i);
    fflush(stdout);
    return false;
  }

  if (j != 0 && !pprod_precedes(r, t)) {
    printf("tree not ordered at node %"PRIu32" (for right child = %"PRIu32")\n", x, j);
    fflush(stdout);
    return false;
  }

  return is_ordered(b, i) && is_ordered(b, j);
}

// ordering constraints for the full tree
static bool tree_is_ordered(rba_buffer_t *b) {
  return is_ordered(b, b->root);
}


/*
 * Check color of node x
 */
static inline bool is_red(rba_buffer_t *b, uint32_t x) {
  assert(x < b->num_nodes);
  return tst_bit(b->isred, x);
}

static inline bool is_black(rba_buffer_t *b, uint32_t x) {
  return ! is_red(b, x);
}

// check color constraints for the subtree rooted at x
static bool check_colors(rba_buffer_t *b, uint32_t x) {
  bool good;
  uint32_t i, j;

  if (x == 0) {
    good = is_black(b, x);
    if (!good) {
      printf("error: null node is not black\n");
      fflush(stdout);
    }
    return good;
  }

  i = b->child[x][0];
  j = b->child[x][1];
  if (is_red(b, x) && (is_red(b, i) || is_red(b, j))) {
    printf("bad coloring at red node %"PRIu32": its two children should be black\n", x);
    fflush(stdout);

    return false;
  }

  return check_colors(b, i) && check_colors(b, j);
}

// coloring constraints for the whole tree
static bool tree_is_well_colored(rba_buffer_t *b) {
  uint32_t x;

  x = b->root;
  if (is_red(b, x)) {
    printf("bad coloring: the root %"PRIu32" is read\n", x);
    fflush(stdout);
    return false;
  }

  return check_colors(b, x);
}


/*
 * Check that the tree is balanced (same number of black nodes
 * on all paths to leaves).
 * - return true if so, and set *h to the number of black nodes
 */
// number of black nodes on paths from x to leaves
static bool is_balanced(rba_buffer_t *b, uint32_t x, uint32_t *h) {
  uint32_t i, j;
  uint32_t hi, hj;

  if (x == 0) {
    assert(is_black(b, x));
    *h = 1;
    return true;
  }

  i = b->child[x][0]; // left child
  j = b->child[x][1]; // right child
  if (is_balanced(b, i, &hi) && is_balanced(b, j, &hj)) {
    if (hi == hj) {
      if (is_black(b, x)) {
	hi ++;
      }
      *h = hi;

      return true;
    } else {
      printf("unbalanced tree at node %"PRIu32"\n", x);
      printf("   left child = %"PRIu32",  black height = %"PRIu32"\n", i, hi);
      printf("  right child = %"PRIu32",  black height = %"PRIu32"\n", j, hj);
      fflush(stdout);
    }
  }
  return false;
}

static bool tree_is_balanced(rba_buffer_t *b) {
  uint32_t h;
  return is_balanced(b, b->root, &h);
}


/*
 * Check size
 * - size of the tree must be equal to num_terms
 * - size of the free list must be equak to num_nodes - num_terms - 1
 */

// size of subtree rooted at x
static uint32_t subtree_size(rba_buffer_t *b, uint32_t x) {
  uint32_t i, j;

  if (x == 0) return 0;

  i = b->child[x][0];
  j = b->child[x][1];
  return 1 + subtree_size(b, i) + subtree_size(b, j);
}

// size of the full tree
static uint32_t tree_size(rba_buffer_t *b) {
  return subtree_size(b, b->root);
}

// size of the free list
static uint32_t free_list_size(rba_buffer_t *b) {
  uint32_t n, i;

  n = 0;
  i = b->free_list;
  while (i != 0) {
    n ++;
    i = b->child[i][0];
  }

  return n;
}

// check
static bool check_sizes(rba_buffer_t *b) {
  uint32_t s;

  s = tree_size(b);
  if (s != b->nterms) {
    printf("invalid tree: size = %"PRIu32", nterms = %"PRIu32"\n", s, b->nterms);
    fflush(stdout);
    return false;
  }

  s = free_list_size(b);
  if (s != b->num_nodes - b->nterms - 1) {
    printf("invalid free list: size = %"PRIu32", should be %"PRIu32"\n",
	   s, b->num_nodes - b->nterms - 1);
    fflush(stdout);
    return false;
  }

  return true;
}


/*
 * All checks
 */
static void check_tree(rba_buffer_t *b) {
  if (!tree_is_ordered(b) || !tree_is_well_colored(b) ||
      !tree_is_balanced(b) || !check_sizes(b)) {
    exit(1);
  }
}


/*
 * Full height: longest path from node x to a leag
 */
static uint32_t node_height(rba_buffer_t *b, uint32_t x) {
  uint32_t i, j, hi, hj;

  if (x == 0) return 0;

  i = b->child[x][0];
  j = b->child[x][1];
  hi = node_height(b, i);
  hj = node_height(b, j);
  if (hi > hj) {
    return hi + 1;
  } else {
    return hj + 1;
  }
}

static uint32_t tree_height(rba_buffer_t *b) {
  return node_height(b, b->root);
}

/*
 * Test node addition: p = power_product to add
 */
static void test_add(rba_buffer_t *b, pprod_t *p) {
  uint32_t i, j, k;
  bool new_node;

  if (p == empty_pp) {
    printf("test add: empty product\n");
  } else {
    printf("test add: x%"PRId32"\n", var_of_pp(p));
  }

  i = rba_find_node(b, p);
  j = rba_get_node(b, p, &new_node);
  k = rba_find_node(b, p);

  if (j != k) {
    printf("Error in test_add: find after get failed\n");
    fflush(stdout);
    exit(1);
  }

  if (i == 0 && !new_node) {
    printf("Error in test_add: expected a new node\n");
    fflush(stdout);
    exit(1);
  }

  if (i != 0) {
    if (new_node) {
      printf("Error in test_add: not expecting a new node\n");
      fflush(stdout);
      exit(1);
    }

    if (j != i) {
      printf("Error in test_add: get returned an unexpected node\n");
      fflush(stdout);
      exit(1);
    }
  }

  check_tree(b);
}


/*
 * Test node removal: p = power_product to remove
 */
static void test_remove(rba_buffer_t *b, pprod_t *p) {
  uint32_t i, j;
  bool new_node;

  if (p == empty_pp) {
    printf("test remove: empty product\n");
  } else {
    printf("test remove: x%"PRId32"\n", var_of_pp(p));
  }

  i = rba_find_node(b, p);
  if (i != 0) {
    q_clear(&b->mono[i].coeff);
    // get_node must be called first to setup b->stack
    j = rba_get_node(b, p, &new_node);
    if (j != i && new_node) {
      printf("Error in test_removed: get_node failed\n");
      fflush(stdout);
      exit(1);
    }
    rba_delete_node(b, i);
    j = rba_find_node(b, p);
    if (j != 0) {
      printf("Error in test_remove: removal failed\n");
      fflush(stdout);
      exit(1);
    }

    check_tree(b);
  }
}

/*
 * Array of power products
 */
#define NUM_TESTS 4000

static pprod_t *test[NUM_TESTS];

static int32_t random_var() {
  return random() & 0xFFFF;
}

static void init_tests(void) {
  uint32_t i;
  int32_t x;

  for (i=0; i<NUM_TESTS; i++) {
    x = random_var();
    test[i] = var_pp(x);
  }

  // force some tests to have the empty power product
  i = random() % NUM_TESTS;
  test[i] = empty_pp;

  i = random() % NUM_TESTS;
  test[i] = empty_pp;
}


/*
 * Tests: add and remove
 */
static void run_tests(rba_buffer_t *b) {
  uint32_t i, h, n;

  check_tree(b);
  init_tests();

  // add all power products
  n = NUM_TESTS;
  for (i=0; i<n; i++) {
    test_add(b, test[i]);
  }
  printf("\nAfter %"PRIu32" additions\n", n);
  printf("   num_nodes = %"PRIu32"\n", b->num_nodes);
  printf("   num_terms = %"PRIu32"\n", b->nterms);
  printf("   root node = %"PRIu32"\n", b->root);
  if (is_balanced(b, b->root, &h)) {
    printf("   b-height    = %"PRIu32"\n", h);
    printf("   full height = %"PRIu32"\n", tree_height(b));
  } else {
    printf("   not balanced\n");
  }
  printf("\n");

  // remove half
  n = NUM_TESTS/2;
  for (i=0; i<n; i++) {
    test_remove(b, test[i]);
  }
  printf("\nAfter %"PRIu32" removals\n", n);
  printf("   num_nodes = %"PRIu32"\n", b->num_nodes);
  printf("   num_terms = %"PRIu32"\n", b->nterms);
  printf("   root node = %"PRIu32"\n", b->root);
  if (is_balanced(b, b->root, &h)) {
    printf("   b-height    = %"PRIu32"\n", h);
    printf("   full height = %"PRIu32"\n", tree_height(b));
  } else {
    printf("   not balanced\n");
  }

  // add them back
  for (i=0; i<n; i++) {
    test_add(b, test[i]);
  }
  printf("\nAfter %"PRIu32" additions\n", n);
  printf("   num_nodes = %"PRIu32"\n", b->num_nodes);
  printf("   num_terms = %"PRIu32"\n", b->nterms);
  printf("   root node = %"PRIu32"\n", b->root);
  if (is_balanced(b, b->root, &h)) {
    printf("   b-height    = %"PRIu32"\n", h);
    printf("   full height = %"PRIu32"\n", tree_height(b));
  } else {
    printf("   not balanced\n");
  }
  printf("\n");


  // Try again after reset
  reset_rba_buffer(b);
  n = NUM_TESTS/2;
  i = n;
  while (i > 0) {
    i --;
    test_add(b, test[i]);
  }

  printf("\nAfter %"PRIu32" additions\n", n);
  printf("   num_nodes = %"PRIu32"\n", b->num_nodes);
  printf("   num_terms = %"PRIu32"\n", b->nterms);
  printf("   root node = %"PRIu32"\n", b->root);
  if (is_balanced(b, b->root, &h)) {
    printf("   b-height    = %"PRIu32"\n", h);
    printf("   full height = %"PRIu32"\n", tree_height(b));
  } else {
    printf("   not balanced\n");
  }
  printf("\n");

  i = n;
  while (i > 0) {
    i --;
    test_remove(b, test[i]);
  }

  printf("\nAfter %"PRIu32" removals\n", n);
  printf("   num_nodes = %"PRIu32"\n", b->num_nodes);
  printf("   num_terms = %"PRIu32"\n", b->nterms);
  printf("   root node = %"PRIu32"\n", b->root);
  if (is_balanced(b, b->root, &h)) {
    printf("   b-height    = %"PRIu32"\n", h);
    printf("   full height = %"PRIu32"\n", tree_height(b));
  } else {
    printf("   not balanced\n");
  }



  fflush(stdout);
}


static pprod_table_t ptable;
static rba_buffer_t buffer;;


int main(void) {
  init_rationals();
  init_pprod_table(&ptable, 0);
  init_rba_buffer(&buffer, &ptable);

  run_tests(&buffer);

  delete_rba_buffer(&buffer);
  delete_pprod_table(&ptable);
  cleanup_rationals();
  return 0;
}
