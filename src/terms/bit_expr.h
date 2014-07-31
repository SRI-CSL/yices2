/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * XOR/OR/NOT graph used to represent intermediate bit-vector expressions.
 *
 * We need a new representation to replace BDDs. The BDDs blow
 * up on several benchmarks.
 *
 * Update: January 29, 2009.
 * - Tests show that flattening the nodes is dangerous. It can consume
 *   a lot of memory and the node table blows up on one QF_BV benchmark.
 * - Since flattening does not work, it makes sense to simplify the
 *   data structures. All OR and XOR nodes are now binary nodes.
 *
 * February 09, 2009:
 * - Added sets of variables to each node
 *
 * April 2010:
 * - adjusted this module to the new term representations
 * - added a new node type (select k i) for bit-select
 * - added a map field to support conversion from bit representation
 *   to boolean terms
 * - removed the vsets
 */

#ifndef __BIT_EXPR_H
#define __BIT_EXPR_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/int_vectors.h"
#include "utils/int_hash_tables.h"


/*
 * The graph is stored as a table of nodes
 * - each node is identified by a 30 bit index in the table
 * - negations are encoded by attaching a polarity bit to a node index:
 *   a node occurrence u_i is a 32 bit integer formatted as
 *     [0|node index|polarity bit]
 *   polarity 0 means positive occurrence
 *   polarity 1 means negative occurrence
 * - there are five types of nodes
 *   - the constant node: 0
 *   - variable node: (term-idx i) where i is an integer
 *   - select node: (select k i) where k and i are integers
 *   - OR nodes: (OR a b)
 *   - XOR nodes: (XOR a b)
 *   where a and b are node occurrences
 *
 * (term-idx i) is intended to denote boolean term i in the term table
 *
 * (select k i) is intended to be bit k of term i where i
 * is a bitvector term in the term table.
 *
 * The constant, variable, and select nodes are the leaf nodes
 * in the DAG. The OR and XOR nodes are non-leaf nodes.
 */

/*
 * Tags identifying the node type
 */
typedef enum {
  UNUSED_NODE,    // deleted node
  CONSTANT_NODE,  // 0 = true
  VARIABLE_NODE,
  SELECT_NODE,
  OR_NODE,
  XOR_NODE,
} node_kind_t;


/*
 * Bit type = 32bit integers
 */
typedef int32_t bit_t;
typedef int32_t node_t;


/*
 * Conversion from node index to bit
 */
static inline bit_t pos_bit(node_t x) {
  return (x<<1)|0;
}

static inline bit_t neg_bit(node_t x) {
  return (x<<1)|1;
}

// sign = 0 or 1 (0 means positive, 1 means negative)
static inline bit_t mk_bit(node_t x, uint32_t sign) {
  assert((sign & ~1) == 0);
  return (x<<1)|sign;
}

static inline bool bit_is_pos(bit_t x) {
  return (x & 1) == 0;
}

static inline bool bit_is_neg(bit_t x) {
  return (x & 1) != 0;
}

static inline node_t node_of_bit(bit_t x) {
  return (x >> 1);
}

// sign = 1 --> negative bit, sign = 0 --> positive bit
static inline uint32_t sign_of_bit(bit_t x) {
  return ((uint32_t) x) & 1;
}

// force the sign bit to 0 (convert (neg_bit(b) to pos_bit(b))
static inline bit_t unsigned_bit(bit_t x) {
  return (x & ~1);
}

// check whether x == (not y)
static inline bool opposite_bits(bit_t x, bit_t y) {
  return (x ^ y) == 1;
}



/*
 * Predefined nodes and bits
 */
enum {
  null_node = -1,
  constant_node = 0,

  null_bit = -1,
  true_bit = 0,
  false_bit = 1,
};




/*
 * Node descriptor:
 * - either an integer (for a variable node)
 * - of a pair index, var (for a select node)
 * - or a pair of bits (for a binary node).
 */
typedef struct select_node_s {
  uint32_t index;
  int32_t var;
} select_node_t;

typedef union node_desc_u {
  int32_t var;
  select_node_t sel;
  bit_t c[2];
} node_desc_t;



/*
 * Global table of nodes. For each node k, we keep
 * - kind[k] = UNUSED/CONSTANT/VARIABLE/OR/XOR
 * - desc[k] = descriptor
 * - map[k] = integer (used in conversion from bits to Boolean terms)
 *   map[k] is set to -1 when the node is created
 *   map[k] is the term corresponding to node k after conversion to terms
 *    (cf. bit_term_conversion)
 *
 * Free list: the UNUSED nodes are stored in a free list
 * - table->free_list = index of the first node in that list
 * - for an UNUSED node i, table->desc[i].var = next node in the free list
 *
 * Auxiliary structures:
 * - vector for simplifying OR and XOR
 * - hash table for hash consing of OR and XOR nodes
 *
 * Garbage collection:
 * - crude technique: we keep a global reference counter for the whole
 *   node table. The counter is the number of external objects that refer
 *   to nodes in the table.
 * - when the counter is zero we reset the whole table
 */
typedef struct node_table_s {
  uint8_t *kind;
  node_desc_t *desc;
  int32_t *map;
  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;

  uint32_t ref_counter;

  ivector_t aux_buffer;
  int_htbl_t htbl;
} node_table_t;


#define DEF_NODE_TABLE_SIZE 1000
#define MAX_NODE_TABLE_SIZE (UINT32_MAX/sizeof(node_desc_t))





/*
 * INITIALIZATION/NODE CONSTRUCTION
 */


/*
 * Initialize node table
 * - n = initial size
 * - if n = 0, the default size is used
 * Also create the constant node
 */
extern void init_node_table(node_table_t *table, uint32_t n);

/*
 * Delete the full node table
 */
extern void delete_node_table(node_table_t *table);

/*
 * Empty the table (but keep the constant node)
 */
extern void reset_node_table(node_table_t *table);




/*
 * CONSTRUCTORS
 */

/*
 * Create a variable node
 * - p = external term index
 */
extern bit_t node_table_alloc_var(node_table_t *table, int32_t p);


/*
 * Create a select node:
 * - k = index
 * - p = external term
 */
extern bit_t node_table_alloc_select(node_table_t *table, uint32_t k, int32_t p);


/*
 * Construct (not x)
 */
static inline bit_t bit_not(bit_t b) {
  return b ^ 1;
}

/*
 * Create a constant bit of value equal to tt
 */
static inline bit_t bit_constant(bool tt) {
  return false_bit - ((uint32_t) tt);
}

/*
 * Conversion of constant bit to integers:
 * - true_bit --> 1, false_bit --> 0
 */
static inline uint32_t bit_const_value(bit_t b) {
  assert(b == true_bit || b == false_bit);
  return b ^ 1;
}


/*
 * Main constructors: don't do much simplification
 */
extern bit_t bit_or2(node_table_t *table, bit_t b1, bit_t b2);
extern bit_t bit_xor2(node_table_t *table, bit_t b1, bit_t b2);

// Variant implementations: simplify more
extern bit_t bit_or2simplify(node_table_t *table, bit_t b1, bit_t b2);
extern bit_t bit_xor2simplify(node_table_t *table, bit_t b1, bit_t b2);


/*
 * Derived operations:
 * (and b1 b2) = ~(or ~b1 ~b2)
 *  (eq b1 b2) = ~(xor b1 b2)
 */
static inline bit_t bit_and2(node_table_t *table, bit_t b1, bit_t b2) {
  return bit_not(bit_or2(table, bit_not(b1), bit_not(b2)));
}

static inline bit_t bit_eq2(node_table_t *table, bit_t b1, bit_t b2) {
  return bit_not(bit_xor2(table, b1, b2));
}

static inline bit_t bit_and2simplify(node_table_t *table, bit_t b1, bit_t b2) {
  return bit_not(bit_or2simplify(table, bit_not(b1), bit_not(b2)));
}

static inline bit_t bit_eq2simplify(node_table_t *table, bit_t b1, bit_t b2) {
  return bit_not(bit_xor2simplify(table, b1, b2));
}



/*
 * N-ary constructors
 * (bit_or  b[0] ... b[n-1])
 * (bit_and b[0] ... b[n-1])
 * (bit_xor b[0] ... b[n-1])
 */
extern bit_t bit_or(node_table_t *table, bit_t *b, uint32_t n);
extern bit_t bit_and(node_table_t *table, bit_t *b, uint32_t n);
extern bit_t bit_xor(node_table_t *table, bit_t *b, uint32_t n);





/*
 * GARBAGE COLLECTION
 */
// increment the reference counter
static inline void node_table_incref(node_table_t *table) {
  table->ref_counter ++;
}

// decrement the reference counter
// if it becomes zero, empty the table.
extern void node_table_decref(node_table_t *table);


// force the reference counter to zero: use this before an explicit call to reset
static inline void node_table_clear_refcount(node_table_t *table) {
  table->ref_counter = 0;
}




/*
 * ACCESS TO THE TABLE
 */
static inline bool valid_node(node_table_t *table, node_t x) {
  return 0 <= x && x < table->nelems;
}

static inline node_kind_t node_kind(node_table_t *table, node_t x) {
  assert(valid_node(table, x));
  return table->kind[x];
}

static inline bool good_node(node_table_t *table, node_t x) {
  return valid_node(table, x) && table->kind[x] != UNUSED_NODE;
}

static inline bool is_constant_node(node_table_t *table, node_t x) {
  return node_kind(table, x) == CONSTANT_NODE;
}

static inline bool is_variable_node(node_table_t *table, node_t x) {
  return node_kind(table, x) == VARIABLE_NODE;
}

static inline bool is_select_node(node_table_t *table, node_t x) {
  return node_kind(table, x) == SELECT_NODE;
}

static inline bool is_or_node(node_table_t *table, node_t x) {
  return node_kind(table, x) == OR_NODE;
}

static inline bool is_xor_node(node_table_t *table, node_t x) {
  return node_kind(table, x) == XOR_NODE;
}

static inline bool is_leaf_node(node_table_t *table, node_t x) {
  node_kind_t k;
  k = node_kind(table, x);
  return k == CONSTANT_NODE || k == VARIABLE_NODE || k == SELECT_NODE;
}

static inline bool is_nonleaf_node(node_table_t *table, node_t x) {
  node_kind_t k;
  k = node_kind(table, x);
  return k == OR_NODE || k == XOR_NODE;
}



/*
 * Get or set map[x] for a node x
 * - the default value for map[x] is -1.
 */
static inline int32_t map_of_node(node_table_t *table, node_t x) {
  assert(good_node(table, x));
  return table->map[x];
}

static inline void set_map_of_node(node_table_t *table, node_t x, int32_t v) {
  assert(good_node(table, x));
  table->map[x] = v;
}



/*
 * Variable of a variable node x
 */
static inline int32_t var_of_node(node_table_t *table, node_t x) {
  assert(is_variable_node(table, x));
  return table->desc[x].var;
}


/*
 * Variable and index of a select node x
 */
static inline select_node_t *select_of_node(node_table_t *table, node_t x) {
  assert(is_select_node(table, x));
  return &table->desc[x].sel;
}

static inline int32_t var_of_select_node(node_table_t *table, node_t x) {
  return select_of_node(table, x)->var;
}

static inline uint32_t index_of_select_node(node_table_t *table, node_t x) {
  return select_of_node(table, x)->index;
}



/*
 * Children of node x = array of 2 bits
 * - x must be a non-leaf node
 */
static inline bit_t *children_of_node(node_table_t *table, node_t x) {
  assert(is_nonleaf_node(table, x));
  return table->desc[x].c;
}

// child 0 or 1
static inline bit_t child_of_node(node_table_t *table, node_t x, uint32_t k) {
  assert(is_nonleaf_node(table, x) && k < 2);
  return table->desc[x].c[k];
}

// left child = child 0, right child = child 1
static inline bit_t left_child_of_node(node_table_t *table, node_t x) {
  return child_of_node(table, x, 0);
}

static inline bit_t right_child_of_node(node_table_t *table, node_t x) {
  return child_of_node(table, x, 1);
}


/*
 * Check whether bit-expression b is a constant
 */
static inline bool bit_is_const(bit_t b) {
  return node_of_bit(b) == constant_node;
}


#endif /* __BIT_EXPR_H */
