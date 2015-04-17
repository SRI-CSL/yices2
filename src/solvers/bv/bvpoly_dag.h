/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

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

#include "utils/int_bv_sets.h"
#include "utils/int_hash_map.h"
#include "utils/int_hash_tables.h"
#include "utils/int_vectors.h"
#include "utils/object_stores.h"

#include "terms/bv64_polynomials.h"
#include "terms/bv_constants.h"
#include "terms/bv_polynomials.h"
#include "terms/bvpoly_buffers.h"
#include "terms/power_products.h"


/*
 * There are seven types of nodes:
 * - [leaf x] where x is a bitvector variable
 * - [zero]
 * - [constant a] where a is a non-zero constant
 * - [offset a0 n1] denotes (a0 + n1)
 * - [mono   a0 n1] denotes (a0 * n1)
 * - [prod  n1^d1 ... n_k^d_k] denotes a power product
 * - [sum  n1 + ... + n_k]
 * Where a0 is a constant, and n_t is a node occurrence.
 *
 * The [leaf x] nodes correspond to expressions that don't need
 * compilation (i.e., [leaf x] is compiled to variable x).  The other
 * nodes are expressions to be compiled.
 *
 * A node occurrence encodes bvneg:
 * - given a node index i, then bvp(i) denotes +i
 *   and bvn(i) denotes (bvneg i) = -i.
 * - the sign is encoded in the lower-order bit of a node occurrence:
 *     bvp(i) is (i << 1) | 0
 *     bvn(i) is (i << 1) | 1
 *
 * Constraints:
 * - in [mono a0 n]: n must be a positive occurrence
 * - in [prod n1^d1 ... n_k^d_k]: all n_i's must be positive occurrences
 * - in [sum n1 ... n_k]: the n_i's must not be offset nodes
 *
 * The DAG maintains a mapping from bit-vector variables to node occurrences.
 * - if x is a bitvector polynomial then dag->vmap stores the bvp(n) or
 *   bvn(n) where n is a node index.
 * - we also use a set (dag->vset) to store the set of variables x
 *   that are mapped to some node occurrence.
 *
 * The node descriptors have a common header that includes:
 * - tag: the node type
 * - bitsize: number of bits
 *
 * For offset and monomial nodes: the constant is either a 64bit integer or a
 * pointer to an array of k 32bit words, where k = ceil(bitsize/32).
 *
 * The nodes are organized in three disjoint sets:
 * - leaf nodes
 * - elementary nodes
 * - other nodes
 *
 * A node is elementary if it is of the following forms:
 *   [zero]
 *   [constant a]
 *   [offset a  n]      where n is a leaf
 *   [mono   a * n]     where n is a leaf
 *   [prod n1 * n2]     where n1 and n2 are leaves
 *   [sum  n1 + n2]     where n1 and n2 are leaves
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
 *
 * During compilation, a node i may be replaced by a node occurrence n.
 * We represent this by mapping i to the special descriptor [alias n].
 * The alias nodes are not stored in any of the lists.
 */


/*
 * NODE INDICES AND OCCURRENCES
 */

typedef int32_t bvnode_t;
typedef int32_t node_occ_t;

#define MAX_NODE (INT32_MAX/2)

static inline node_occ_t bvp(bvnode_t i) {
  assert(0 <= i && i <= MAX_NODE);
  return i << 1;
}

static inline node_occ_t bvn(bvnode_t i) {
  assert(0 <= i && i <= MAX_NODE);
  return (i << 1) | 1;
}

static inline bvnode_t node_of_occ(node_occ_t n) {
  assert(0 <= n);
  return (n >> 1);
}

static inline uint32_t sign_of_occ(node_occ_t n) {
  return (uint32_t) (n & 1);
}

// flip the sign
static inline node_occ_t negate_occ(node_occ_t n) {
  return n ^ 1;
}

// remove the sign
static inline node_occ_t unsigned_occ(node_occ_t n) {
  return n & ~1;
}



/*
 * NODE DESCRIPTORS
 */
typedef enum bvc_tag {
  BVC_LEAF,
  BVC_ZERO,
  BVC_CONSTANT,
  BVC_OFFSET,
  BVC_MONO,
  BVC_PROD,
  BVC_SUM,
  BVC_ALIAS,
} bvc_tag_t;

typedef struct bvc_header_s {
  bvc_tag_t tag;
  uint32_t bitsize;
} bvc_header_t;

typedef struct bvc_leaf_s {
  bvc_header_t header;
  int32_t  map; //  variable the leaf is compiled to
} bvc_leaf_t;

// zero: no attributes except the bitsize
typedef struct bvc_zero_s {
  bvc_header_t header;
} bvc_zero_t;

typedef struct bvc_constant_s {
  bvc_header_t header;
  union {
    uint64_t c;
    uint32_t *w;
  } value;
} bvc_constant_t;

typedef struct bvc_offset_s {
  bvc_header_t header;
  node_occ_t nocc;
  union {
    uint64_t c;
    uint32_t *w;
  } constant;
} bvc_offset_t;

typedef struct bvc_mono_s {
  bvc_header_t header;
  node_occ_t nocc;
  union {
    uint64_t c;
    uint32_t *w;
  } coeff;
} bvc_mono_t;


/*
 * Product
 * - varexp_t is a pair var/exponent defined in power_products.h
 * - hash = bitmask based on the nodes occurring in the products
 * - len = number of pairs in the power product
 * - prod = array of size elements
 * The actual operands are stored in prod[0..len-1] but
 * size may be more than len.
 */
typedef struct bvc_prod_s {
  bvc_header_t header;
  uint32_t hash;
  uint32_t size;
  uint32_t len;
  varexp_t prod[0];
} bvc_prod_t;

#define MAX_BVC_PROD_LEN (UINT32_MAX/sizeof(varexp_t))


/*
 * Sum:
 * - each integer in the sum array is either +n or -n for some node index n
 * - len = number of elements in the sum
 * - hash = bitmask
 * - sum = array of size elements (size >= len)
 * The operands are in sum[0 .. len-1].
 */
typedef struct bvc_sum_s {
  bvc_header_t header;
  uint32_t hash;
  uint32_t size;
  uint32_t len;
  node_occ_t sum[0]; // real size = len (when allocated)
} bvc_sum_t;

#define MAX_BVC_SUM_LEN (UINT32_MAX/sizeof(int32_t))


typedef struct bvc_alias_s {
  bvc_header_t header;
  node_occ_t alias;
} bvc_alias_t;


/*
 * Access to descriptors from a pointer to the header
 */
static inline bool node_is_leaf(bvc_header_t *d) {
  return d->tag == BVC_LEAF;
}

static inline bool node_is_zero(bvc_header_t *d) {
  return d->tag == BVC_ZERO;
}

static inline bool node_is_constant(bvc_header_t *d) {
  return d->tag == BVC_CONSTANT;
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

static inline bool node_is_alias(bvc_header_t *d) {
  return d->tag == BVC_ALIAS;
}

static inline bvc_leaf_t *leaf_node(bvc_header_t *d) {
  assert(node_is_leaf(d));
  return (bvc_leaf_t *) d;
}

static inline bvc_zero_t *zero_node(bvc_header_t *d) {
  assert(node_is_zero(d));
  return (bvc_zero_t *) d;
}

static inline bvc_constant_t *bvconst_node(bvc_header_t *d) {
  assert(node_is_constant(d));
  return (bvc_constant_t *) d;
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

static inline bvc_alias_t *alias_node(bvc_header_t *d) {
  assert(node_is_alias(d));
  return (bvc_alias_t *) d;
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
 * - vmap = map variable x to +/-n, where n is a DAG node index
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
  object_store_t zero_store;
  object_store_t constant_store;
  object_store_t offset_store;
  object_store_t mono_store;
  object_store_t prod_store;  // for binary products
  object_store_t sum_store1;  // for sums of len <= 4
  object_store_t sum_store2;  // for sums of len between 4 and 8
  object_store_t alias_store;

  // auxiliary buffers
  bvconstant_t aux;
  pp_buffer_t pp_aux;
  bvpoly_buffer_t poly_buffer;
  ivector_t buffer;
} bvc_dag_t;


#define DEF_BVC_DAG_SIZE 500
#define MAX_BVC_DAG_SIZE ((UINT32_MAX/sizeof(bvc_item_t)) - 2)


// max len of products and sums allocated in the stores
// for larger size, descriptors are allocated using safe_malloc
#define PROD_STORE_LEN 2
#define SUM_STORE1_LEN 4
#define SUM_STORE2_LEN 8

// list-header indices: three main lists
#define BVC_DAG_LEAF_LIST    0
#define BVC_DAG_ELEM_LIST    (-1)
#define BVC_DAG_DEFAULT_LIST (-2)
#define BVC_DAG_AUX_LIST     (-3)


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
 * Checks on a node n
 */
static inline bvc_tag_t bvc_dag_node_type(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return dag->desc[n]->tag;
}

static inline bool bvc_dag_node_is_leaf(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_leaf(dag->desc[n]);
}

static inline bool bvc_dag_node_is_zero(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_zero(dag->desc[n]);
}

static inline bool bvc_dag_node_is_constant(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_constant(dag->desc[n]);
}

static inline bool bvc_dag_node_is_offset(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_offset(dag->desc[n]);
}

static inline bool bvc_dag_node_is_mono(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_mono(dag->desc[n]);
}

static inline bool bvc_dag_node_is_prod(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_prod(dag->desc[n]);
}

static inline bool bvc_dag_node_is_sum(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_sum(dag->desc[n]);
}

static inline bool bvc_dag_node_is_alias(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return node_is_alias(dag->desc[n]);
}

static inline bvc_leaf_t *bvc_dag_node_leaf(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return leaf_node(dag->desc[n]);
}

static inline bvc_zero_t *bvc_dag_node_zero(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return zero_node(dag->desc[n]);
}

static inline bvc_constant_t *bvc_dag_node_constant(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return bvconst_node(dag->desc[n]);
}

static inline bvc_offset_t *bvc_dag_node_offset(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return offset_node(dag->desc[n]);
}

static inline bvc_mono_t *bvc_dag_node_mono(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return mono_node(dag->desc[n]);
}

static inline bvc_prod_t *bvc_dag_node_prod(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return prod_node(dag->desc[n]);
}

static inline bvc_sum_t *bvc_dag_node_sum(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return sum_node(dag->desc[n]);
}

static inline bvc_alias_t *bvc_dag_node_alias(bvc_dag_t *dag, bvnode_t n) {
  assert(0 < n && n <= dag->nelems);
  return alias_node(dag->desc[n]);
}


// more checks with n a node_occurrence
static inline bool bvc_dag_occ_is_leaf(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_leaf(dag, node_of_occ(n));
}

static inline bool bvc_dag_occ_is_zero(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_zero(dag, node_of_occ(n));
}

static inline bool bvc_dag_occ_is_constant(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_constant(dag, node_of_occ(n));
}

static inline bool bvc_dag_occ_is_offset(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_offset(dag, node_of_occ(n));
}

static inline bool bvc_dag_occ_is_mono(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_mono(dag, node_of_occ(n));
}

static inline bool bvc_dag_occ_is_prod(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_prod(dag, node_of_occ(n));
}

static inline bool bvc_dag_occ_is_sum(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_sum(dag, node_of_occ(n));
}

static inline bool bvc_dag_occ_is_alias(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_is_alias(dag, node_of_occ(n));
}



/*
 * Check whether n is a shared node occurrence
 * (i.e., +n or -n occur more than once)
 */
extern bool bvc_dag_occ_is_shared(bvc_dag_t *dag, node_occ_t n);




/*
 * MAPPING VARIABLES --> NODES
 */

/*
 * Check whether x is in vset (i.e., there's a node attached to x)
 */
static inline bool bvc_dag_var_is_present(bvc_dag_t *dag, int32_t x) {
  assert(x > 0);
  return int_bvset_member(&dag->vset, x);
}


/*
 * Get the node occurrence mapped to x
 */
static inline node_occ_t bvc_dag_nocc_of_var(bvc_dag_t *dag, int32_t x) {
  assert(bvc_dag_var_is_present(dag, x));
  return int_hmap_find(&dag->vmap, x)->val;
}


/*
 * Store mapping [x --> n]
 * - x must be positive
 * - x must not be mapped already (not in vset)
 */
extern void bvc_dag_map_var(bvc_dag_t *dag, int32_t x, node_occ_t n);


/*
 * NODE CONSTRUCTION
 */

/*
 * Create a leaf node mapped to x
 * - x must be positive
 * - x must not be mapped (i.e., not in dag->vset)
 * - creates q := [leaf x]
 * - returns bvp(q)
 */
extern node_occ_t bvc_dag_leaf(bvc_dag_t *dag, int32_t x, uint32_t bitsize);


/*
 * Get a node mapped to x
 * - if there isn't one, create a leaf node [leaf x]
 */
extern node_occ_t bvc_dag_get_nocc_of_var(bvc_dag_t *dag, int32_t x, uint32_t bitsize);


/*
 * Variable of a leaf node-occurrence n
 */
static inline int32_t bvc_dag_get_var_of_leaf(bvc_dag_t *dag, node_occ_t n) {
  return bvc_dag_node_leaf(dag, node_of_occ(n))->map;
}


/*
 * Compilation result for node_occurrence n:
 * - modulo signs, this is the variable of n if n is a leaf node
 *   or the variable of n' if n is aliased to n'
 * - to encode the signs, we return either bvp(x) or bvn(x)
 *   where x is a variable
 *     bvp(x) means that n is compiled to x
 *     bvn(x) means that n is compiled to (bvneg x)
 * - in all other cases, the function returns -1
 */
extern int32_t bvc_dag_get_nocc_compilation(bvc_dag_t *dag, node_occ_t n);


/*
 * Construct a monomial node q
 * - a must be normalized modulo 2^bitsize
 * - depending on the coefficient a and the sign of n:
 *        q := [mono a n] and returns bvp(q)
 *     or q := [mono (-a) n] and returns bvn(q)
 *     or q := [mono a (-n)] and returns bvn(q)
 *     or q := [mono (-a) (-n)] and returns bvp(q)
 *
 * There are two versions: one for bitsize <= 64, one for bitsize > 64.
 */
extern node_occ_t bvc_dag_mono64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize);
extern node_occ_t bvc_dag_mono(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize);


/*
 * Construct an offset node q
 * - a must be normalized modulo 2^bitsize
 * - this creates q := [offset a n] and returns q
 * There are two versions: one for bitsize <= 64, one for bitsize > 64.
 */
extern node_occ_t bvc_dag_offset64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize);
extern node_occ_t bvc_dag_offset(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize);



/*
 * Construct a power product node q
 * - q is defined by the exponents in power product p and the
 *   nodes in array a: if p is x_1^d_1 ... x_k^d_k
 *   then a must have k elements a[0] ... a[k-1]
 * - if all a[i] are positive, then q is [prod a[0]^d_1 ... a[k-1]^d_k]
 * - otherwise, signs are adjusted to ensure that all nodes in the product
 *   have positive sign. Then the result q is either the positive or negative
 *   occurrence of the product (depending on the sign of a[i]s and on
 *   whether the exponents are odd or even).
 */
extern node_occ_t bvc_dag_pprod(bvc_dag_t *dag, pprod_t *p, node_occ_t *a, uint32_t bitsize);


/*
 * Construct a sum node q
 * - a = array of n node occurrences
 * - n must be positive
 *
 * If n == 1, this returns a[0].
 * Otherwise, a is sorted and a node q := [sum a[0] ... a[n-1]] is created
 */
extern node_occ_t bvc_dag_sum(bvc_dag_t *dag, node_occ_t *a, uint32_t n, uint32_t bitsize);


/*
 * Convert a polynomial p to a DAG node q and return q
 * - q is defined by the coefficients in p and
 *   the node occurrences in array a
 * - p must be non-zero and non-constant: it's of the
 *   form  b_0 x_0 + b_1 x_1 + ... + b_k x_k  where k >= 1.
 * - array a must have k+1 elements a[0] ... a[k]
 *
 * If x_0 is const_idx then a[0] is ignored and q is the root node for
 * (b_0 + b_1 a[1] + ... + b_k a[k]).  Otherwise, q is the root node
 * for (b_0 a[0] + b_1 a[1] + ... + b_k a[k]).
  */
extern node_occ_t bvc_dag_poly64(bvc_dag_t *dag, bvpoly64_t *p, node_occ_t *a);
extern node_occ_t bvc_dag_poly(bvc_dag_t *dag, bvpoly_t *p, node_occ_t *a);


/*
 * Same thing for a polynomial p stored in buffer b
 * - b must be normalized and non-constant
 */
extern node_occ_t bvc_dag_poly_buffer(bvc_dag_t *dag, bvpoly_buffer_t *b, node_occ_t *a);




/*
 * ITERATION THROUGH THE LISTS
 */

/*
 * First node in one of the three node lists (a negative index means that the list is empty)
 */
static inline bvnode_t bvc_first_leaf(bvc_dag_t *dag) {
  return dag->list[BVC_DAG_LEAF_LIST].next;
}

static inline bvnode_t bvc_first_elem_node(bvc_dag_t *dag) {
  return dag->list[BVC_DAG_ELEM_LIST].next;
}

static inline bvnode_t bvc_first_complex_node(bvc_dag_t *dag) {
  return dag->list[BVC_DAG_DEFAULT_LIST].next;
}


/*
 * Move node i to the auxiliary list (remove i from the leaf/elem/complex
 * list first).
 */
extern void bvc_move_node_to_aux_list(bvc_dag_t *dag, bvnode_t i);

/*
 * Move the auxiliary list to the elem/complex list
 */
extern void bvc_move_aux_to_elem_list(bvc_dag_t *dag);
extern void bvc_move_aux_to_complex_list(bvc_dag_t *dag);



/*
 * Length of each list
 */
extern uint32_t bvc_num_leaves(bvc_dag_t *dag);
extern uint32_t bvc_num_elem_nodes(bvc_dag_t *dag);
extern uint32_t bvc_num_complex_nodes(bvc_dag_t *dag);



/*
 * REDUCTION
 */

/*
 * Convert node i to a leaf node (for variable x)
 * - i must not be a leaf or alias node
 */
extern void bvc_dag_convert_to_leaf(bvc_dag_t *dag, bvnode_t i, int32_t x);


/*
 * Replace all occurrences of {n1, n2} in sums by n
 * - a node p = [sum ... n1 ... n2 ...] is rewritten to [sum ... n ... ...]
 *   a node p = [sum ... neg(n1) .. neg(n2) ...] is rewritten to [sum ... neg(n) .. ...]
 */
extern void bvc_dag_reduce_sum(bvc_dag_t *dag, node_occ_t n, node_occ_t n1, node_occ_t n2);


/*
 * Replace all occurrences of {n1, n2} in products by n
 * - n, n1, and n2 must be positive occurrences
 */
extern void bvc_dag_reduce_prod(bvc_dag_t *dag, node_occ_t n, node_occ_t n1, node_occ_t n2);


/*
 * Check whether there is a sum node that can be reduced by +n1 +n2 or -n1 -n2
 * - n1 and n2 must be distinct
 */
extern bool bvc_dag_check_reduce_sum(bvc_dag_t *dag, node_occ_t n1, node_occ_t n2);


/*
 * Check whether there's a product node that can be reduced by n1 * n2
 */
extern bool bvc_dag_check_reduce_prod(bvc_dag_t *dag, node_occ_t n1, node_occ_t n2);



/*
 * Add an elementary node to enable reduction of at least one non-elementary node
 * - the list of non-elementary node must not be empty
 */
extern void bvc_dag_force_elem_node(bvc_dag_t *dag);




#endif /* __BVPOLY_DAG_H */
