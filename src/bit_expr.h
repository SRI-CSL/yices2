/*
 * XOR/OR/NOT graph used to represent bit-vector expressions
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
 */

#ifndef __BIT_EXPR_H
#define __BIT_EXPR_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "int_vectors.h"
#include "int_hash_tables.h"
#include "int_hash_sets.h"
#include "int_queues.h"
#include "vsets.h"

/*
 * The graph is stored as a table of nodes
 * - each node is identified by a 30 bit index in the table
 * - negations are encoded by attaching a polarity bit to a node index:
 *   a node occurrence u_i is a 32 bit integer formatted as
 *     [0|node index|polarity bit]
 *   polarity 0 means positive occurrence
 *   polarity 1 measn negative occurrence
 * - there are four types of nodes
 *   - the constant node: 0
 *   - variable nodes X (each attached to an external variable in the bv_var_manager)
 *   - OR nodes: (OR a b) 
 *   - XOR nodes: (XOR a b) 
 *   where a and b are node occurrences
 */

/*
 * Tags identifying the node type
 */
typedef enum {
  UNUSED_NODE,    // deleted node
  CONSTANT_NODE,  // 0 = true
  VARIABLE_NODE,
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

// sign = 0 or 1
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
 * Node desciptor:
 * - either an integer (for a bitvector variable)
 * - or a pair of bits (for a binary node).
 */
typedef union node_desc_u {
  int32_t var;
  bit_t c[2];
} node_desc_t;


/*
 * Cache to accelerate the computation of union_vset
 * - just keep the arguments and results of the previous
 *   call to union_vset.
 */
typedef struct uvset_cache_s {
  vset_t *last_left;
  vset_t *last_right;
  vset_t *last_result;
} uvset_cache_t;


/*
 * Global table of nodes. For each node k, we keep
 * - kind[k] = UNUSED/CONSTANT/VARIABLE/OR/XOR
 * - desc[k] = descriptor
 * - vars[k] = vector of theory variables occurring in k
 *
 * During garbage collection, the high-order bit of kind[k]
 * is used as a mark.
 *
 * Free list: the UNUSED nodes are stored in a free list
 * - table->free_list = index of the first node in that list
 * - for an UNUSED node i, table->desc[i].var = next node in the free list
 *
 * Auxiliary structures:
 * - vector for simplifying OR and XOR
 * - hash table for hash consing of OR and XOR nodes
 * - queue: to explore the DAG breadth-first
 * - int_hash_set allocated on demand. It's used to collect nodes.
 * - vtbl: table of vsets
 * - cache: cache of union
 */
typedef struct node_table_s {
  uint8_t *kind;
  node_desc_t *desc;
  vset_t **vars;
  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;

  ivector_t aux_buffer;
  int_htbl_t htbl;
  vset_htbl_t vtbl;
  uvset_cache_t cache;
  int_queue_t queue;  
  int_hset_t *node_set;  
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
 * The node_set is not created (NULL).
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
 * Create a variable
 * - p = the attached external variable
 */
extern bit_t node_table_alloc_var(node_table_t *table, int32_t p);

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
  // (int32_t) true = 1, false -> 1
  return false_bit - ((int32_t) tt);
}

/*
 * Conversion of constant bit to integers:
 * - true_bit --> 1, false_bit --> 0
 */
static inline int32_t bit_const_value(bit_t b) {
  assert(b == true_bit || b == false_bit);
  return 1 - b;
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
 * UTILITIES
 */


/*
 * Get the internal node set. Allocate and initialized it if needed.
 */
extern int_hset_t *node_table_get_node_set(node_table_t *table);


/*
 * Delete the internal node set. Do nothing if the set hasn't been allocated.
 */
extern void node_table_delete_node_set(node_table_t *table);



/*
 * Collect the nodes reachable from b into set
 * - set must be empty and initialized
 * - the result is in compacted form (cf. int_hset_close)
 */
extern void collect_bitexpr_nodes(node_table_t *table, bit_t b, int_hset_t *set);

/*
 * Add all nodes reachable from b[0] ... b[n-1] to set
 * - set mut be initialized
 * - the result is not compacted
 */
extern void collect_bitarray_nodes(node_table_t *table, uint32_t n, bit_t *b, int_hset_t *set);


/*
 * SUPPORT FOR GARBAGE COLLECTION
 */

/*
 * Marker object to visit a set of nodes
 * - each node is visited once
 * - a callback function is called the first time a node is reached
 * - the callback function takes two arguments:
 *   1) a pointer to the marking object itself
 *   2) the index of the node reached
 * The node table must be unchanged when this is used
 *
 * After marking: the caller must clear all the marks
 * (optionally, also delete the unmarked nodes)
 */

typedef struct bit_marking_obj_s bit_marking_obj_t;

typedef void (*bit_marking_callback_t)(void *, node_t);

struct bit_marking_obj_s {
  node_table_t *table;
  bit_marking_callback_t fun; // callback function
};


/*
 * Initialize a marking object
 * - f = the callback function
 */
static inline void init_bit_marker(bit_marking_obj_t *marker, node_table_t *table, 
				   bit_marking_callback_t f) {
  marker->table = table;
  marker->fun = f;
}


/*
 * Visit all nodes reachable from x:
 * - use depth-first search
 * - all nodes not reached before are marked and the callback function is called
 */
extern void bit_marker_visit(bit_marking_obj_t *marker, node_t x);


/*
 * End of marking: clear all the marks
 */
extern void node_table_clear_marks(node_table_t *table);


/*
 * End or marking: clear the marks and delete the unmarked nodes
 * (Garbage collection)
 */
extern void node_table_garbage_collection(node_table_t *table);






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

static inline bool is_or_node(node_table_t *table, node_t x) {
  return node_kind(table, x) == OR_NODE;
}

static inline bool is_xor_node(node_table_t *table, node_t x) {
  return node_kind(table, x) == XOR_NODE;
}

static inline bool is_leaf_node(node_table_t *table, node_t x) {
  node_kind_t k;
  k = node_kind(table, x);
  return k == CONSTANT_NODE || k == VARIABLE_NODE;
}

static inline bool is_nonleaf_node(node_table_t *table, node_t x) {
  node_kind_t k;
  k = node_kind(table, x);
  return k == OR_NODE || k == XOR_NODE;
}


/*
 * Bitvector variable attached to node x
 * - x must be a variable node
 */
static inline int32_t bv_var_of_node(node_table_t *table, node_t x) {
  assert(is_variable_node(table, x));
  return table->desc[x].var;
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
 * Variables of node x 
 */
static inline vset_t *vars_of_node(node_table_t *table, node_t x) {
  assert(good_node(table, x));
  return table->vars[x];
}



/*
 * Check whether bit-expression b is a constant
 */
static inline bool bit_is_const(bit_t b) {
  return node_of_bit(b) == constant_node;
}


#endif /* __BIT_EXPR_H */
