/*
 * DAG OF BIT-VECTOR EXPRESSIONS
 */

/*
 * When converting bitvector polynomials to elementary expression,
 * we use an intermediate DAG representation (cf. bvpoly_compiler.h).
 * The DAG attempts to maximize sharing of subexpressions (so
 * that bit-blasting works better).
 */

#ifndef __BVPOLY_DAG_H
#define __BVPOLY_DAG_H

#include <assert.h>
#include <stdint.h>

#include "int_vectors.h"
#include "object_stores.h"
#include "int_bv_sets.h"
#include "int_hash_map.h"
#include "int_hash_tables.h"

#include "bv_constants.h"
#include "power_products.h"
#include "bv64_polynomials.h"
#include "bv_polynomials.h"


/*
 * There are five types of nodes:
 * - leaves: variables (defined in the bv_vartable)
 * - offsets: expressions (a0 +/- n) where a0 is a constant, n is a node
 * - monomials: expressions (a0 * n) where a0 is a constant, n is a node
 * - products: (n1^d1 ... n_k^d_k): power product:: n_1,...,n_k are nodes
 * - sums:    (+/-n1 .... +/-n_k); sum of of a_i n_i, where a_i is either +1 or -1.
 *
 * The leave nodes correspond to expressions that don't need compilation.
 * The other nodes are expressions to be compiled.
 *
 * The node descriptors have a common header that includes:
 * - tag: the node type
 * - var: variable mapped to this node or (-1)
 * - bitsize: number of bits
 *
 * For offset and monomial nodes: the constant is either a 64bit integer or a
 * pointer to an array of k 32bit words, where k = ceil(bitize/32).
 *
 * The nodes are organized in three disjoint sets:
 * - leaf nodes
 * - elementary nodes
 * - other nodes
 *
 * A node is elementary if it is of the following forms:
 *   [offset a +/- n]   where n is a leaf
 *   [mono   a * n]     where n is a leaf
 *   [prod n1 * n2]     where n1 and n2 are leaves
 *   [sum +/-n1 +/-n2]  where n1 and n2 are leaves
 *
 * The compilation process replaces elementary nodes an elementary
 * node n by a leaf node (so new nodes may become elementary as a
 * result)..
 * 
 *
 * Each node is identified by a positive integer n
 * - for node n, we store 
 *     desc[n] = node descriptor
 *     use[n] = index of nodes that contain +n or -n
 * - to represent the sets leaf/elementary/other nodes:
 *   we use an array indexed from -2 to the number of nodes - 1
 *     list[i].pre: predecessor in circular list
 *     list[i].next: successor
 *   the three elements list[-2], list[-1], list[0] are headers
 *   for the lists of non-elementary, elementary, leaf nodes, respectively.
 */

typedef enum bvc_tag {
  BVC_LEAF,
  BVC_OFFSET,
  BVC_MONO,
  BVC_PROD,
  BVC_SUM,
} bvc_tag_t;

typedef struct bvc_header_s {
  bvc_tag_t tag;
  int32_t  var;
  uint32_t bitsize;
} bvc_header_t;

typedef struct bvc_leaf_s {
  bvc_header_t header;
} bvc_leaf_t;

typedef struct bvc_offset_s {
  bvc_header_t header;
  int32_t node;
  union {
    uint64_t c;
    uint32_t *w;
  } constant;
} bvc_offset_t;

typedef struct bvc_mono_s {
  bvc_header_t header;
  int32_t node;
  union {
    uint64_t c;
    uint32_t *w;
  } coeff;
} bvc_mono_t;


/*
 * Product
 * varexp_t is a pair var/exponent definied in power_products.h
 * hash = bitmask based on the nodes occurring in the products
 * len = number of pairs in the power product 
 * prod = array of len elements
 */
typedef struct bvc_prod_s {
  bvc_header_t header;
  uint32_t hash;
  uint32_t len;
  varexp_t prod[0];
} bvc_prod_t;

#define MAX_BVC_PROD_LEN (UINT32_MAX/sizeof(varexp_t))


/*
 * Sum:
 * - each integer in the sum array is either +n or -n for some node index n
 * - len = number of elements in the sum
 * - hash = bitmasak
 */
typedef struct bvc_sum_s {
  bvc_header_t header;
  uint32_t hash;
  uint32_t len;
  int32_t sum[0]; // real size = len (when allocated)
} bvc_sum_t;

#define MAX_BVC_SUM_LEN (UINT32_MAX/sizeof(int32_t))



/*
 * Access to descriptors from a pointer to the header
 */
static inline bool node_is_leaf(bvc_header_t *d) {
  return d->tag == BVC_LEAF;
}

static inline bool node_is_offset(bvc_header_t *d) {
  return d->tag == BVC_OFFSET;
}

static inline bool node_is_mono(bvc_header_t *d) {
  return d->tag == BVC_MONO;
}

static inline bool node_is_prod(bvc_header_t *d) {
  return d->tag == BVC_PROD;
}

static inline bool node_is_sum(bvc_header_t *d) {
  return d->tag == BVC_SUM;
}

static inline bvc_leaf_t *leaf_node(bvc_header_t *d) {
  assert(node_is_leaf(d));
  return (bvc_leaf_t *) d;
}

static inline bvc_offset_t *offset_node(bvc_header_t *d) {
  assert(node_is_offset(d));
  return (bvc_offset_t *) d;
}

static inline bvc_mono_t *mono_node(bvc_header_t *d) {
  assert(node_is_mono(d));
  return (bvc_mono_t *) d;
}

static inline bvc_prod_t *prod_node(bvc_header_t *d) {
  assert(node_is_prod(d));
  return (bvc_prod_t *) d;
}

static inline bvc_sum_t *sum_node(bvc_header_t *d) {
  assert(node_is_sum(d));
  return (bvc_sum_t *) d;
}





/*
 * DAG Structure
 */

/*
 * Elements in the circular lists
 */
typedef struct bvc_item_s {
  int32_t pre;
  int32_t next;
} bvc_item_t;

/*
 * To keep track of the nodes mapped to a variable x:
 * - vset = set of variables mapped to an existing node
 * - vmap = map variable x of vars to a node n in the DAG
 */
typedef struct bvc_dag_s {
  // node descriptors + use lists + node sets
  bvc_header_t **desc;
  int32_t **use;  
  bvc_item_t *list;
  uint32_t nelems;   // number of nodes (i.e., desc[1]  ... desc[nelems] are non-NULL)
  uint32_t size;     // size of arrays desc and use

  int_htbl_t htbl; // for hash consing

  // mapping from variables to nodes
  int_bvset_t vset;
  int_hmap_t vmap;

  // stores for descriptor allocation
  object_store_t leaf_store;
  object_store_t offset_store;
  object_store_t mono_store;
  object_store_t prod_store;  // for binary products
  object_store_t sum_store1;  // for sums of len <= 4
  object_store_t sum_store2;  // for sums of len between 4 and 8

  // auxiliary buffers
  bvconstant_t aux;
  ivector_t buffer;
} bvc_dag_t;


#define DEF_BVC_DAG_SIZE 500
#define MAX_BVC_DAG_SIZE ((UINT32_MAX/sizeof(bvc_item_t)) - 2)


// max len of products and sums allocated in the stores
// for larger size, descriptors are allocated using safe_malloc
#define PROD_STORE_LEN 2
#define SUM_STORE1_LEN 4
#define SUM_STORE2_LEN 8



/*
 * OPERATIONS
 */

/*
 * Initialize: n = initial size
 * - if n=0, the default size is used
 */
extern void init_bvc_dag(bvc_dag_t *dag, uint32_t n);


/*
 * Delete all
 */
extern void delete_bvc_dag(bvc_dag_t *dag);


/*
 * Empty the DAG
 */
extern void reset_bvc_dag(bvc_dag_t *dag);



/*
 * NODE CONSTRUCTION
 */

/*
 * Create a leaf node for variable x
 * - x must be positive
 * - x must not be mapped (i.e., not in dag->vset)
 * - returns node index n and stores the mapping [x --> n]
 *   in dag->vmap.
 */
extern int32_t bvc_dag_add_leaf(bvc_dag_t *dag, int32_t x, uint32_t bitsize);

/*
 * Convert a polynomial expression of a variable x to a node n
 * - x must be positive
 * - there mustn't be a node mapped to x yet
 * - store the mapping [x --> n] in dag->vmap
 * - return the node index
 *
 * All variables of p that are not mapped already are converted to
 * leaf nodes.
 */
extern int32_t bvc_dag_add_pprod(bvc_dag_t *dag, int32_t x, pprod_t *p, uint32_t bitsize);
extern int32_t bvc_dag_add_poly64(bvc_dag_t *dag, int32_t x, bvpoly64_t *p);
extern int32_t bvc_dag_add_poly(bvc_dag_t *dag, int32_t x, bvpoly_t *p);





#endif /* __BVPOLY_DAG_H */
