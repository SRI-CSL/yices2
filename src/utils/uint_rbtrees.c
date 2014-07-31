/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * RED-BLACK TREES TO STORE SETS OF UNSIGNED 32-BIT INTEGERS
 */

#include "utils/memalloc.h"
#include "utils/uint_rbtrees.h"


/*
 * Initialize tree
 * - n = initial size
 * - if n = 0, the default size is used
 */
void init_rbtree(rbtree_t *tree, uint32_t n) {
  if (n == 0) {
    n = DEF_RBTREE_SIZE;
  }
  if (n >= MAX_RBTREE_SIZE) {
    out_of_memory();
  }

  tree->data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  tree->node = (rbnode_t *) safe_malloc(n * sizeof(rbnode_t));
  tree->isred = allocate_bitvector(n);
  tree->size = n;
  init_ivector(&tree->stack, 20);

  assert(n > 0 && null_rbnode == 0);

  // initialize the null_node
  tree->data[0] = 0;
  tree->node[0][0] = 0;
  tree->node[0][1] = 0;
  clr_bit(tree->isred, 0); // black node

  tree->nbnodes = 1;
  tree->root = 0;
}


/*
 * Resize the tree: make it 50% larger
 */
static void extend_rbtree(rbtree_t *tree) {
  uint32_t n;

  n = tree->size + 1;
  n += n>>1;
  if (n >= MAX_RBTREE_SIZE) {
    out_of_memory();
  }

  tree->data = (uint32_t *) safe_realloc(tree->data, n * sizeof(uint32_t));
  tree->node = (rbnode_t *) safe_realloc(tree->node, n * sizeof(rbnode_t));
  tree->isred = extend_bitvector(tree->isred, n);
  tree->size = n;
}


/*
 * Allocate a new node and return its id
 * - the node is not initialized
 */
static uint32_t rbtree_new_node(rbtree_t *tree) {
  uint32_t i;

  i = tree->nbnodes;
  if (i == tree->size) {
    extend_rbtree(tree);
  }
  assert(i < tree->size);
  tree->nbnodes = i+1;

  return i;
}


/*
 * Delete tree: free memory
 */
void delete_rbtree(rbtree_t *tree) {
  safe_free(tree->data);
  safe_free(tree->node);
  delete_bitvector(tree->isred);
  delete_ivector(&tree->stack);
  tree->data = NULL;
  tree->node = NULL;
  tree->isred = NULL;
}


/*
 * Reset: empty the tree
 */
void reset_rbtree(rbtree_t *tree) {
  tree->nbnodes = 1;
  tree->root = null_rbnode;
  ivector_reset(&tree->stack);
}


/*
 * Search for a node of value x
 * - return its id or null_rbnode if there's no such node
 */
uint32_t rbtree_find(rbtree_t *tree, uint32_t x) {
  uint32_t i, k;

  // to force termination: store x in the null_node
  tree->data[0] = x;

  i = tree->root;
  assert(i < tree->nbnodes);
  while (tree->data[i] != x) {
    k = (tree->data[i] < x);
    assert((k == 0 && x < tree->data[i]) ||
           (k == 1 && x > tree->data[i]));
    i = tree->node[i][k];
    assert(i < tree->nbnodes);
  }

  return i;
}



/*
 * Auxiliary functions for balancing the tree
 */

/*
 * Check whether p is parent of q
 * - both must be valid node indices
 */
#ifndef NDEBUG
static inline bool is_parent_node(rbtree_t *tree, uint32_t p, uint32_t q) {
  assert(p < tree->nbnodes && q < tree->nbnodes);
  return tree->node[p][0] == q || tree->node[p][1] == q;
}
#endif

/*
 * Child-index(p, q):
 * - q must be a child of node p
 * - returns 0 if q is the left child
 *   returns 1 if q is the right child
 * So i = child_index(treee, p, q) implies tree->node[p][i] = q
 */
static inline uint32_t child_index(rbtree_t *tree, uint32_t p, uint32_t q) {
  assert(is_parent_node(tree, p, q));
  return tree->node[p][1] == q;
}


/*
 * Get sibling of q in p
 * - both p and q must be valid node indices
 * - q must be a child of p
 */
static inline uint32_t sibling(rbtree_t *tree, uint32_t p, uint32_t q) {
  assert(is_parent_node(tree, p, q));
  return (tree->node[p][0] ^ tree->node[p][1]) ^ q;
}


/*
 * Check color of node p
 */
static inline bool is_red(rbtree_t *tree, uint32_t p) {
  assert(p < tree->nbnodes);
  return tst_bit(tree->isred, p);
}

#ifndef NDEBUG
static inline bool is_black(rbtree_t *tree, uint32_t p) {
  return ! is_red(tree, p);
}
#endif

/*
 * Set the color of node p
 */
static inline void mark_red(rbtree_t *tree, uint32_t p) {
  assert(p < tree->nbnodes);
  set_bit(tree->isred, p);
}

static inline void mark_black(rbtree_t *tree, uint32_t p) {
  assert(p < tree->nbnodes);
  clr_bit(tree->isred, p);
}


/*
 * Balance the tree:
 * - p = new node just added (must be red)
 * - q = parent of p
 * - tree->stack contains [null_rbnode, root, ..., r],
 *   which describes a path form the root to r where r = parent of q.
 * - the root must be black
 */
static void rbtree_balance(rbtree_t *tree, uint32_t p, uint32_t q) {
  uint32_t r, s;
  uint32_t i, j;

  assert(is_parent_node(tree, q, p) && is_red(tree, p) && is_black(tree, tree->root));

  while (is_red(tree, q)) {
    r = ivector_pop2(&tree->stack); // r = parent of q
    assert(is_black(tree, r));

    s = sibling(tree, r, q);       // s = sibling of q
    if (is_red(tree, s)) {
      // flip colors of q and s
      mark_black(tree, s);
      mark_black(tree, q);
      // if r is the root, we're done
      if (r == tree->root) break;
      // otherwise, we color r red
      // and move up to p := r, q := parent of r
      mark_red(tree, r);
      p = r;
      q = ivector_pop2(&tree->stack); // q = parent of r
      assert(is_parent_node(tree, q, p));

    } else {
      // Balance the tree with one or two rotations
      i = child_index(tree, r, q);
      j = child_index(tree, q, p);
      if (i != j) {
        /*
         * Rotate p and q
         * q becomes a child of p
         * p becomes a child of r
         */
        assert(q != 0 && p != 0 && r != 0 &&
               tree->node[r][i] == q &&
               tree->node[q][j] == p);
        tree->node[r][i] = p;
        tree->node[q][j] = tree->node[p][i];
        tree->node[p][i] = q;

        // prepare for second rotation:
        q = p;
      }

      /*
       * rotate r and q
       * and fix the colors: r becomes red, q becomes black
       */
      assert(tree->node[r][i] == q);
      p = ivector_pop2(&tree->stack);
      if (p == null_rbnode) {
        assert(r == tree->root);
        tree->root = q;
      } else {
        // p is r's parent
        j = child_index(tree, p, r);
        assert(tree->node[p][j] == r);
        tree->node[p][j] = q;
      }
      tree->node[r][i] = tree->node[q][1-i];
      tree->node[q][1-i] = r;
      mark_red(tree, r);
      mark_black(tree, q);

      break;
    }
  }
}



/*
 * Search or add node of value x
 * - return the node id
 * - set new_node to true if that's a new node (x was not present)
 */
uint32_t rbtree_get(rbtree_t *tree, uint32_t x, bool *new_node) {
  uint32_t k, i, p;

  assert(tree->stack.size == 0);

  // to force termination: store x in the null_node
  tree->data[0] = x;

  k = 0; // stop GCC bogus warning
  p = null_rbnode; // parent
  i = tree->root;
  assert(i < tree->nbnodes);
  while (tree->data[i] != x) {
    k = (tree->data[i] < x);
    assert((k == 0 && x < tree->data[i]) ||
           (k == 1 && x > tree->data[i]));

    // save p on the stack for balancing
    ivector_push(&tree->stack, p);
    p = i;
    i = tree->node[i][k];
    assert(i < tree->nbnodes);
  }

  *new_node = false;
  if (i == 0) {
    // x is not in the current tree: add it
    *new_node = true;

    i = rbtree_new_node(tree);
    tree->data[i] = x;
    tree->node[i][0] = null_rbnode;
    tree->node[i][1] = null_rbnode;
    if (p == null_rbnode) {
      // make sure the root is always black
      tree->root = i;
      mark_black(tree, i);
    } else {
      // add i as child of p then balance the tree
      assert(p < tree->nbnodes && tree->node[p][k] == null_rbnode);
      tree->node[p][k] = i;
      mark_red(tree, i);
      rbtree_balance(tree, i, p);
    }
  }

  ivector_reset(&tree->stack);

  assert(i > 0 && tree->data[i] == x);

  return i;
}



/*
 * To scan the tree:
 * - return the id of the node whose value is the smallest
 *   element in the tree that's >= x.
 * - return null_rbnode (i.e., 0) if all elements are smaller than x.
 */
uint32_t rbtree_find_sup(rbtree_t *tree, uint32_t x) {
  uint32_t i, j;

  // to force termination: store x in the null_node
  tree->data[0] = x;

  // j = either null_node or
  // such that tree->data[j] > x
  j = null_rbnode;
  i = tree->root;
  while (tree->data[i] != x) {
    if (tree->data[i] < x) {
      i = tree->node[i][1];
    } else {
      j = i;
      i = tree->node[i][0];
    }
  }

  if (i > 0) {
    assert(tree->data[i] == x);
    return i;
  } else {
    return j;
  }
}



#if 0

/*
 * Search or add node of value x
 * - return the node id
 * - set new_node to true if that's a new node (x was not present)
 * Don't balance the tree
 */
uint32_t rbtree_get_var(rbtree_t *tree, uint32_t x, bool *new_node) {
  uint32_t k, i, p;

  // to force termination: store x in the null_node
  tree->data[0] = x;

  k = 0; // stop GCC bogus warning
  p = null_rbnode; // parent
  i = tree->root;
  assert(i < tree->nbnodes);
  while (tree->data[i] != x) {
    k = (tree->data[i] < x);
    assert((k == 0 && x < tree->data[i]) ||
           (k == 1 && x > tree->data[i]));

    p = i;
    i = tree->node[i][k];
    assert(i < tree->nbnodes);
  }

  *new_node = false;
  if (i == 0) {
    // x is not in the current tree: add it
    *new_node = true;

    i = rbtree_new_node(tree);
    tree->data[i] = x;
    tree->node[i][0] = null_rbnode;
    tree->node[i][1] = null_rbnode;
    mark_black(tree, i);

    if (p == null_rbnode) {
      tree->root = i;
    } else {
      assert(p < tree->nbnodes && tree->node[p][k] == null_rbnode);
      tree->node[p][k] = i;
    }
  }

  assert(i > 0 && tree->data[i] == x);

  return i;
}

#endif
