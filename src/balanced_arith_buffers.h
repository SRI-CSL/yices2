/*
 * BUFFER FOR ARITHMETIC OPERATIONS USING RED-BLACK TREES
 */

/*
 * The arith_buffers represent polynomials as lists of monomials.
 * This makes some operations inefficient (if the list is long).
 * On some of the SMT-LIB 2 QF_LIA/miplib benchmarks, this causes
 * a  major slow down (polynomial construction takes minutes).
 *
 * This module is an alternative representation based on balanced binary trees.
 */

#ifndef __BALANCED_ARITH_BUFFERS_H
#define __BALANCED_ARITH_BUFFERS_H

#include <stdint.h>
#include <assert.h>

#include "bitvectors.h"
#include "int_vectors.h"
#include "rationals.h"
#include "pprod_tables.h"
#include "polynomials.h"


/*
 * Buffer = tree of monomials.
 * 
 * Each node in the tree is identified by an index (uint32_t)
 * - index 0 = null_node)is a marker for leaves
 * - other nodes have an index between 1 and nterms
 *
 * The tree is represented using three arrasy:
 * - mono[i] = monomial for node i
 * - node[i] = pair of children: 
 *   node[i][0] = left child, node[i][1] = right child
 *   (if i is a leed node then left and right children are 0)
 * - isred[i] = one bit: 1 means red node, 0 means black node
 *
 * Global data:
 * - size = size of arrays mono, node, isred
 * - nterms = total number of terms
 * - root = id of the root node (or null_node for the empty tree)
 * - ptbl = pprod table for constuction of power products
 * - stack = vector used for balancing = path form root to a new node
 */

// monomial structure = pair power product/rational
typedef struct mono_s {
  pprod_t *prod;
  rational_t coeff;
} mono_t;

// node = array of two indices
typedef uint32_t rb_node_t[2];

enum {
  rb_null_node = 0;
};

// tree structure
typedef struct rb_arith_buffer_s {
  mono_t *mono;
  rb_node_t *node;
  byte_t *isred;
  pprod_t *ptbl;
  ivector_t stack;
  uint32_t size;
  uint32_t nterms;
  uint32_t root;
} rb_arith_buffer_t;


/*
 * Default and maximal size
 */
#define DEF_RB_ARITH_BUFFER_SIZE 64
#define MAX_RB_ARITH_BUFFER_SIZE (UINT32_MAX/sizeof(mono_t))


/*
 * OPERATIONS
 */

/*
 * Initialize:
 * - ptbl = attached power product table
 * - the buffer contains the empty tree (i.e., zero polynomial)
 */
extern void init_rb_arith_buffer(rb_arith_buffer_t *b, pprod_table_t *ptbl);

/*
 * Delete: free all memory
 */
extern void delete_rb_arith_buffer(rb_arith_buffer_t *b);

/*
 * Reset (to the empty tree)
 */
extern void reset_rb_arith_buffer(rb_arith_buffer_t *b);


/*
 * Normalize: remove 


#endif /* __BALANCED_ARITH_BUFFERS_H */
