/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * RED-BLACK TREES TO STORE SETS OF UNSIGNED 32-BIT INTEGERS
 * - elements are sorted in increasing order
 */

#ifndef __UINT_RBTREES_H
#define __UINT_RBTREES_H

#include <stdint.h>
#include <assert.h>

#include "utils/bitvectors.h"
#include "utils/int_vectors.h"

/*
 * Each node in the tree is identified by an uint32_t index.
 * - null_node = 0 is a marker (for leaves)
 * - non-leaf nodes have an index between 1 and nbnodes - 1
 *
 * A binary tree is represented using three arrays:
 * - data[i] = value of node i
 * - node[i] = pair of children:
 *   node[i][0] = left child, node[i][1] = right child
 * - isred[i] = one bit per node: 1 means red node, 0 means black node
 *
 * Global data:
 * - size = size of arrays data, node, isred
 * - nbnodes = number of nodes in the tree
 * - root = id of the root node (or null_node if the tree is empty)
 *
 * Auxiliary data:
 * - stack = vector to record the path from the root to a node
 */
typedef uint32_t rbnode_t[2];

enum {
  null_rbnode = 0,
};

typedef struct rbtree_s {
  uint32_t *data;
  rbnode_t *node;
  byte_t *isred;  // bitvector
  ivector_t stack;
  uint32_t size;
  uint32_t nbnodes;
  uint32_t root;
} rbtree_t;


/*
 * Default and maximal size = maximal number of nodes
 */
#define DEF_RBTREE_SIZE 250
#define MAX_RBTREE_SIZE (UINT32_MAX/sizeof(rbnode_t))


/*
 * OPERATIONS
 */

/*
 * Initialize tree
 * - n = initial size. If n is zero, the default is used.
 * - the null_node is created and colored black
 * - the tree is empty: root = null_node
 */
extern void init_rbtree(rbtree_t *tree, uint32_t n);


/*
 * Delete tree: free memory
 */
extern void delete_rbtree(rbtree_t *tree);


/*
 * Reset: empty the tree
 */
extern void reset_rbtree(rbtree_t *tree);


/*
 * Search for a node i with data[i] = x
 * - return null_rbnode (i.e., 0), it there's no such i
 */
extern uint32_t rbtree_find(rbtree_t *tree, uint32_t x);


/*
 * Search for a node i with data[i] = x. If there's none
 * create a new node for x and return its index.
 * Maintain the tree balanced.
 * - in both cases, return i such that data[i] = x,
 *   with i != null_rbnode
 * - *new_node is set to true if i is a new node
 * - *new_node is false otherwise
 */
extern uint32_t rbtree_get(rbtree_t *tree, uint32_t x, bool *new_node);


/*
 * To scan the tree:
 * - return the id of the node in tree, whose value is the smallest
 *   element in the tree that's >= x.
 * - return null_rbnose (i.e., 0) if all elements are smaller than x.
 */
extern uint32_t rbtree_find_sup(rbtree_t *tree, uint32_t x);


/*
 * Number of nodes in tree
 */
static inline uint32_t rbtree_num_nodes(rbtree_t *tree) {
  return tree->nbnodes;
}

/*
 * Get the root node
 */
static inline uint32_t rbtree_root(rbtree_t *tree) {
  return tree->root;
}

/*
 * Check whether the tree is empty
 */
static inline bool rbtree_is_empty(rbtree_t *tree) {
  return tree->root == null_rbnode;
}


/*
 * Cardinality = number of non-null nodes
 */
static inline uint32_t rbtree_card(rbtree_t *tree) {
  return tree->nbnodes - 1;
}

/*
 * Check whether x is present in the tree
 */
static inline bool rbtree_is_present(rbtree_t *tree, uint32_t x) {
  return rbtree_find(tree, x) > 0;
}


/*
 * Add x to the tree: no change if x is already in there
 */
static inline void rbtree_add(rbtree_t *tree, uint32_t x) {
  bool new;
  (void) rbtree_get(tree, x, &new);
}


/*
 * Access to node i's components
 */
static inline uint32_t rbtree_node_value(rbtree_t *tree, uint32_t i) {
  assert(i < tree->nbnodes);
  return tree->data[i];
}

static inline uint32_t rbtree_node_left_child(rbtree_t *tree, uint32_t i) {
  assert(i < tree->nbnodes);
  return tree->node[i][0];
}

static inline uint32_t rbtree_node_right_child(rbtree_t *tree, uint32_t i) {
  assert(i < tree->nbnodes);
  return tree->node[i][1];
}


#endif /* __UINT_RBTREES_H */
