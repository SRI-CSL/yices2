/*
 * DAG OF BIT-VECTOR EXPRESSIONS
 */

#include <assert.h>

#include "memalloc.h"
#include "bit_tricks.h"
#include "bv64_constants.h"
#include "index_vectors.h"
#include "hash_functions.h"
#include "int_array_sort.h"

#include "bvpoly_dag.h"



/*
 * LIST OPERATIONS
 */

/*
 * Initialize list[k] to a singleton list
 */
static inline void init_list(bvc_item_t *list, int32_t k) {
  list[k].pre = k;
  list[k].next = k;
}


/*
 * Add i before k in list[k]
 */
static inline void list_add(bvc_item_t *list, int32_t k, int32_t i) {
  int32_t j;

  assert(i != k);

  j = list[k].pre;
  list[j].next = i;
  list[i].pre = j;
  list[i].next = k;
  list[k].pre = i;
}


/*
 * Remove i from its current list
 */
static inline void list_remove(bvc_item_t *list, int32_t i) {
  int32_t j, k;

  j = list[i].pre;
  k = list[i].next;
  list[j].next = k;
  list[k].pre = j;
}



/*
 * Add n to one of the three node lists:
 * - list[0]  --> leaves
 * - list[-1] --> elementary nodes
 * - list[-2] --> default list
 */
static inline void bvc_dag_add_to_leaves(bvc_dag_t *dag, node_t n) {
  assert(0 < n && n <= dag->nelems);
  list_add(dag->list, BVC_DAG_LEAF_LIST, n);
}

static inline void bvc_dag_add_to_elementary_list(bvc_dag_t *dag, node_t n) {
  assert(0 < n && n <= dag->nelems);
  list_add(dag->list, BVC_DAG_ELEM_LIST, n);
}

static inline void bvc_dag_add_to_default_list(bvc_dag_t *dag, node_t n) {
  assert(0 < n && n <= dag->nelems);
  list_add(dag->list, BVC_DAG_DEFAULT_LIST, n);
}


/*
 * Move n to a different list
 */
static inline void bvc_dag_move_to_leaves(bvc_dag_t *dag, node_t n) {
  assert(0 < n && n <= dag->nelems);
  list_remove(dag->list, n);
  list_add(dag->list, BVC_DAG_LEAF_LIST, n);
}

static inline void bvc_dag_move_to_elementary_list(bvc_dag_t *dag, node_t n) {
  assert(0 < n && n <= dag->nelems);
  list_remove(dag->list, n);
  list_add(dag->list, BVC_DAG_ELEM_LIST, n);
}





/*
 * DAG OPERATIONS
 */

/*
 * Initialize dag:
 * - n = initial size. If n=0, use the default size.
 */
void init_bvc_dag(bvc_dag_t *dag, uint32_t n) {
  bvc_item_t *tmp;

  if (n == 0) {
    n = DEF_BVC_DAG_SIZE;
  }
  if (n >= MAX_BVC_DAG_SIZE) {
    out_of_memory();
  }
  assert(n > 0);

  dag->desc = (bvc_header_t **) safe_malloc(n * sizeof(bvc_header_t *));
  dag->use = (int32_t **) safe_malloc(n * sizeof(int32_t *));
  tmp = (bvc_item_t *) safe_malloc((n + 2) * sizeof(bvc_item_t));
  dag->list = tmp + 2;

  dag->desc[0] = NULL;
  dag->use[0] = NULL;
  init_list(dag->list, -2);
  init_list(dag->list, -1);
  init_list(dag->list, 0);  

  dag->nelems = 0;
  dag->size = n;

  init_int_htbl(&dag->htbl, 0);
  init_int_bvset(&dag->vset, 0);  // use bvset default size (1024)
  init_int_hmap(&dag->vmap, 128);

  init_objstore(&dag->leaf_store, sizeof(bvc_leaf_t), 500);
  init_objstore(&dag->offset_store, sizeof(bvc_offset_t), 500);
  init_objstore(&dag->mono_store, sizeof(bvc_mono_t), 500);
  init_objstore(&dag->prod_store, sizeof(bvc_prod_t) + PROD_STORE_LEN * sizeof(varexp_t), 100);
  init_objstore(&dag->sum_store1, sizeof(bvc_sum_t) + SUM_STORE1_LEN * sizeof(int32_t), 500);
  init_objstore(&dag->sum_store2, sizeof(bvc_sum_t) + SUM_STORE2_LEN * sizeof(int32_t), 500);

  init_bvconstant(&dag->aux);
  init_pp_buffer(&dag->pp_aux, 10);
  init_ivector(&dag->buffer, 10);
}



/*
 * Increase the size (by 50%)
 */
static void extend_bvc_dag(bvc_dag_t *dag) {
  bvc_item_t *tmp;
  uint32_t n;

  n = dag->size + 1;
  n += (n >> 1);
  if (n >= MAX_BVC_DAG_SIZE) {
    out_of_memory();
  }

  assert(n > dag->size);

  dag->desc = (bvc_header_t **) safe_realloc(dag->desc, n * sizeof(bvc_header_t *));
  dag->use = (int32_t **) safe_realloc(dag->use, n * sizeof(int32_t *));
  tmp = dag->list - 2;
  tmp = (bvc_item_t *) safe_realloc(tmp, (n + 2) * sizeof(bvc_item_t));
  dag->list = tmp + 2;

  dag->size = n;
}


/*
 * Add a new node n with descriptor d
 * - set use[n] to NULL
 * - list[n] is not initialized
 */
static node_t bvc_dag_add_node(bvc_dag_t *dag, bvc_header_t *d) {
  uint32_t i;

  i = dag->nelems + 1;
  if (i == dag->size) {
    extend_bvc_dag(dag);
  }
  assert(i < dag->size);

  dag->desc[i] = d;
  dag->use[i] = NULL;

  dag->nelems = i;

  return i;
}


/*
 * Free memory used by descriptor d
 * - free d itself if it's not form a store (i.e., d->size is large)
 * - free d->constant.w if d->bitsize > 64
 */
static void delete_descriptor(bvc_header_t *d) {
  switch (d->tag) {
  case BVC_LEAF:
    break;

  case BVC_OFFSET:
    if (d->bitsize > 64) {
      bvconst_free(offset_node(d)->constant.w, (d->bitsize + 31) >> 5);
    }
    break;

  case BVC_MONO:
    if (d->bitsize > 64) {
      bvconst_free(mono_node(d)->coeff.w, (d->bitsize + 31) >> 5);
    }
    break;

  case BVC_PROD:
    if (prod_node(d)->size > PROD_STORE_LEN) {
      safe_free(d);
    }
    break;

  case BVC_SUM:
    if (sum_node(d)->size > SUM_STORE2_LEN) {
      safe_free(d);
    }
    break;
  }
}


/*
 * Delete the DAG
 */
void delete_bvc_dag(bvc_dag_t *dag) {
  uint32_t i, n;

  n = dag->nelems;
  for (i=1; i<=n; i++) {
    delete_descriptor(dag->desc[i]);
    delete_index_vector(dag->use[i]);
  }

  safe_free(dag->desc);
  safe_free(dag->use);
  safe_free(dag->list - 2);

  dag->desc = NULL;
  dag->use = NULL;
  dag->list = NULL;

  delete_int_htbl(&dag->htbl);
  delete_int_bvset(&dag->vset);
  delete_int_hmap(&dag->vmap);

  delete_objstore(&dag->leaf_store);
  delete_objstore(&dag->offset_store);
  delete_objstore(&dag->mono_store);
  delete_objstore(&dag->prod_store);
  delete_objstore(&dag->sum_store1);
  delete_objstore(&dag->sum_store2);

  delete_bvconstant(&dag->aux);
  delete_pp_buffer(&dag->pp_aux);
  delete_ivector(&dag->buffer);
}


/*
 * Empty: remove all nodes
 */
void reset_bvc_dag(bvc_dag_t *dag) {
  uint32_t i, n;

  n = dag->nelems;
  for (i=1; i<=n; i++) {
    delete_descriptor(dag->desc[i]);
    delete_index_vector(dag->use[i]);
  }

  dag->nelems = 0;

  // reset the three lists
  init_list(dag->list, -2);
  init_list(dag->list, -1);
  init_list(dag->list, 0);  

  reset_int_htbl(&dag->htbl);
  reset_int_bvset(&dag->vset);
  int_hmap_reset(&dag->vmap);

  reset_objstore(&dag->leaf_store);
  reset_objstore(&dag->offset_store);
  reset_objstore(&dag->mono_store);
  reset_objstore(&dag->prod_store);
  reset_objstore(&dag->sum_store1);
  reset_objstore(&dag->sum_store2);  

  pp_buffer_reset(&dag->pp_aux);
  ivector_reset(&dag->buffer);
}






/*
 * NODE DESCRIPTOR ALLOCATION
 */

/*
 * Descriptor allocation
 * - for prod and sum, n = length of the sum or product
 */
static inline bvc_leaf_t *alloc_leaf(bvc_dag_t *dag) {
  return (bvc_leaf_t *) objstore_alloc(&dag->leaf_store);
}

static inline bvc_offset_t *alloc_offset(bvc_dag_t *dag) {
  return (bvc_offset_t *) objstore_alloc(&dag->offset_store);
}

static inline bvc_mono_t *alloc_mono(bvc_dag_t *dag) {
  return (bvc_mono_t *) objstore_alloc(&dag->mono_store);
}

static bvc_prod_t *alloc_prod(bvc_dag_t *dag, uint32_t n) {
  void *tmp;

  if (n <= PROD_STORE_LEN) {
    tmp = objstore_alloc(&dag->prod_store);
  } else if (n <= MAX_BVC_PROD_LEN) {
    tmp = safe_malloc(sizeof(bvc_prod_t) + n * sizeof(varexp_t));
  } else {
    out_of_memory();
  }

  return (bvc_prod_t *) tmp;
}

static bvc_sum_t *alloc_sum(bvc_dag_t *dag, uint32_t n) {
  void *tmp;

  if (n <= SUM_STORE1_LEN) {
    tmp = objstore_alloc(&dag->sum_store1);
  } else if (n <= SUM_STORE2_LEN) {
    tmp = objstore_alloc(&dag->sum_store2);
  } else if (n <= MAX_BVC_SUM_LEN) {
    tmp = safe_malloc(sizeof(bvc_sum_t) + n * sizeof(int32_t));
  } else {
    out_of_memory();
  }

  return (bvc_sum_t *) tmp;
}


/*
 * De-allocation
 */
static inline void free_leaf(bvc_dag_t *dag, bvc_leaf_t *d) {
  objstore_free(&dag->leaf_store, d);
}

static void free_offset(bvc_dag_t *dag, bvc_offset_t *d) {
  if (d->header.bitsize > 64) {
    bvconst_free(d->constant.w, (d->header.bitsize + 31) >> 5);
  }
  objstore_free(&dag->offset_store, d);
}

static void free_mono(bvc_dag_t *dag, bvc_mono_t *d) {
  if (d->header.bitsize > 64) {
    bvconst_free(d->coeff.w, (d->header.bitsize + 31) >> 5);
  }
  objstore_free(&dag->mono_store, d);
}

static void free_prod(bvc_dag_t *dag, bvc_prod_t *d) {
  if (d->len <= PROD_STORE_LEN) {
    objstore_free(&dag->prod_store, d);
  } else {
    safe_free(d);
  }
}

static void free_sum(bvc_dag_t *dag, bvc_sum_t *d) {
  if (d->len <= SUM_STORE1_LEN) {
    objstore_free(&dag->sum_store1, d);
  } else if (d->len <= SUM_STORE2_LEN) {
    objstore_free(&dag->sum_store2, d);
  } else {
    safe_free(d);
  }
}



/*
 * Check whether a product or sum node is elementary
 */
static bool prod_node_is_elementary(bvc_dag_t *dag, bvc_prod_t *d) {
  assert(d->len >= 1);

  if (d->len == 1) {
    return d->prod[0].exp == 2 && bvc_dag_occ_is_leaf(dag, d->prod[0].var);
  } else if (d->len == 2) {
    return d->prod[0].exp + d->prod[1].exp == 2 &&
      bvc_dag_occ_is_leaf(dag, d->prod[0].var) &&
      bvc_dag_occ_is_leaf(dag, d->prod[1].var);
  } else {
    return false;
  }    
}

static bool sum_node_is_elementary(bvc_dag_t *dag, bvc_sum_t * d) {
  assert(d->len >= 2);
  return d->len == 2 && bvc_dag_occ_is_leaf(dag, d->sum[0]) && bvc_dag_occ_is_leaf(dag, d->sum[1]);
}



/*
 * NODE CONSTRUCTION
 */

/*
 * Add i to the use list of n
 */
static inline void bvc_dag_add_dependency(bvc_dag_t *dag, node_t n, node_t i) {
  assert(0 < n && n <= dag->nelems && 0 < i && i <= dag->nelems && i != n);
  add_index_to_vector(dag->use + n, i);
}


/*
 * Bit hash: 
 * - for a node index n, the bit_hash is a 32bit word
 *   equal to (1 << (n & 31)): i.e., bit i is set if (n % 32 == i).
 * - for a set of node indices, the bit hash is the bitwise or
 *   of the bit_hash of each element
 *
 * This gives a quick filter to test inclusion between sets of 
 * nodes: if bit_hash(A) & bit_hash(B) != bit_hash(A) then
 * A can't be a subset of B.
 */
static inline uint32_t bit_hash(node_t n) {
  assert(n > 0);
  return ((uint32_t) 1) << (n & 31);
}

static inline uint32_t bit_hash_occ(node_occ_t n) {
  return bit_hash(node_of_occ(n));
}


/*
 * Create a leaf node
 */
static node_t bvc_dag_mk_leaf(bvc_dag_t *dag, int32_t x, uint32_t bitsize) {
  bvc_leaf_t *d;
  node_t q;

  d = alloc_leaf(dag);
  d->header.tag = BVC_LEAF;
  d->header.bitsize = bitsize;
  d->map = x;

  q = bvc_dag_add_node(dag, &d->header);
  bvc_dag_add_to_leaves(dag, q);

  return q;
}


/*
 * Create an offset node q := [offset a n]
 */
static node_t bvc_dag_mk_offset64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize) {
  bvc_offset_t *d;
  node_t q;

  assert(1 <= bitsize && bitsize <= 64 && a == norm64(a, bitsize));

  d = alloc_offset(dag);
  d->header.tag = BVC_OFFSET;
  d->header.bitsize = bitsize;
  d->nocc = n;
  d->constant.c = a;

  q = bvc_dag_add_node(dag, &d->header);
  bvc_dag_add_to_elementary_list(dag, q);
  bvc_dag_add_dependency(dag, node_of_occ(n), q); // q depends on n

  return q;
}


static node_t bvc_dag_mk_offset(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize) {
  bvc_offset_t *d;
  uint32_t *c;
  uint32_t k;
  node_t q;

  assert(bitsize > 64);

  // make a copy of a: a must be normalized so the copy will be normalized too
  k = (bitsize + 31) >> 5;
  c = bvconst_alloc(k);
  bvconst_set(c, k, a);
  assert(bvconst_is_normalized(c, bitsize));

  d = alloc_offset(dag);
  d->header.tag = BVC_OFFSET;
  d->header.bitsize = bitsize;
  d->nocc = n;
  d->constant.w = c;

  q = bvc_dag_add_node(dag, &d->header);
  bvc_dag_add_to_elementary_list(dag, q);
  bvc_dag_add_dependency(dag, node_of_occ(n), q); // q depends on n

  return q;
}



/*
 * Create an monomial node q := [mono a, n]
 */
static node_t bvc_dag_mk_mono64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize) {
  bvc_mono_t *d;
  node_t q;

  assert(1 <= bitsize && bitsize <= 64 && a == norm64(a, bitsize));

  d = alloc_mono(dag);
  d->header.tag = BVC_MONO;
  d->header.bitsize = bitsize;
  d->nocc = n;
  d->coeff.c = a;

  q = bvc_dag_add_node(dag, &d->header);

  bvc_dag_add_to_elementary_list(dag, q);
  bvc_dag_add_dependency(dag, node_of_occ(n), q); // q depends on n

  return q;
}


static node_t bvc_dag_mk_mono(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize) {
  bvc_mono_t *d;
  uint32_t *c;
  uint32_t k;
  node_t q;

  assert(bitsize > 64 && bvconst_is_normalized(a, bitsize));

  // make a copy of a.
  // a must be normalized so the copy will be normalized too
  k = (bitsize + 31) >> 5;
  c = bvconst_alloc(k);
  bvconst_set(c, k, a);
  assert(bvconst_is_normalized(c, bitsize));

  d = alloc_mono(dag);
  d->header.tag = BVC_MONO;
  d->header.bitsize = bitsize;
  d->nocc = n;
  d->coeff.w = c;

  q = bvc_dag_add_node(dag, &d->header);

  bvc_dag_add_to_elementary_list(dag, q);
  bvc_dag_add_dependency(dag, node_of_occ(n), q); // q depends on n

  return q;
}




/*
 * Product node defined by a[0 ... n-1]:
 * - each a[i] is a pair (node, exponent)
 */
static node_t bvc_dag_mk_prod(bvc_dag_t *dag, varexp_t *a, uint32_t n, uint32_t bitsize) {
  bvc_prod_t *d;
  uint32_t i;
  int32_t q, k;

  d = alloc_prod(dag, n);
  d->header.tag = BVC_PROD;
  d->header.bitsize = bitsize;
  d->hash = 0;
  d->size = n;
  d->len = n;
  for (i=0; i<n; i++) {
    d->prod[i] = a[i];
    d->hash |= bit_hash_occ(a[i].var);
  }

  q = bvc_dag_add_node(dag, &d->header);
  for (i=0; i<n; i++) {
    bvc_dag_add_dependency(dag, node_of_occ(a[i].var), q);
  }
  
  k = BVC_DAG_DEFAULT_LIST;
  if (prod_node_is_elementary(dag, d)) {
    k = BVC_DAG_ELEM_LIST;
  }
  list_add(dag->list, k, q);

  return q;
}



/*
 * Sum mode a[0] + ... + a[n-1]
 * - each a[i] is a node occurrence
 */
static node_t bvc_dag_mk_sum(bvc_dag_t *dag, node_occ_t *a, uint32_t n, uint32_t bitsize) {
  bvc_sum_t *d;
  uint32_t i;
  node_t q;
  int32_t k;

  d = alloc_sum(dag, n);
  d->header.tag = BVC_SUM;
  d->header.bitsize = bitsize;
  d->hash = 0;
  d->size = n;
  d->len = n;
  for (i=0; i<n; i++) {
    d->sum[i] = a[i];
    d->hash |= bit_hash_occ(a[i]);
  }

  q = bvc_dag_add_node(dag, &d->header);
  for (i=0; i<n; i++) {
    bvc_dag_add_dependency(dag, node_of_occ(a[i]), q);
  }

  k = BVC_DAG_DEFAULT_LIST;
  if (sum_node_is_elementary(dag, d)) {
    k = BVC_DAG_ELEM_LIST;
  }
  list_add(dag->list, k, q);

  return q;
}


/*
 * HASH CONSING
 */

typedef struct bvc_leaf_hobj_s {
  int_hobj_t m;
  bvc_dag_t *dag;
  uint32_t bitsize;
  int32_t map;
} bvc_leaf_hobj_t;

// same struct for both offset/mono with 64bit constant
typedef struct bvc64_hobj_s {
  int_hobj_t m;
  bvc_dag_t *dag;
  uint64_t c;
  uint32_t bitsize;
  node_occ_t nocc;
} bvc64_hobj_t;

// struct for offset/mono with larger constant
typedef struct bvc_hobj_s {
  int_hobj_t m;
  bvc_dag_t *dag;
  uint32_t *c;
  uint32_t bitsize;
  node_occ_t nocc;
} bvc_hobj_t;

typedef struct bvc_prod_hobj_s {
  int_hobj_t m;
  bvc_dag_t *dag;
  varexp_t *pp;  
  uint32_t bitsize;
  uint32_t len;
} bvc_prod_hobj_t;

typedef struct bvc_sum_hobj_s {
  int_hobj_t m;
  bvc_dag_t *dag;
  node_occ_t *noccs;
  uint32_t bitsize;
  uint32_t len;
} bvc_sum_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_bvc_leaf_hobj(bvc_leaf_hobj_t *p) {
  return jenkins_hash_pair(p->map, 0, 0x12930a32);
}

static uint32_t hash_bvc_offset64_hobj(bvc64_hobj_t *p) {
  uint32_t a, b;

  a = jenkins_hash_uint64(p->c);
  b = jenkins_hash_int32(p->nocc);
  return jenkins_hash_pair(a, b, 0x23da32aa);
}

static uint32_t hash_bvc_offset_hobj(bvc_hobj_t *p) {
  uint32_t a, b;

  a = bvconst_hash(p->c, p->bitsize);
  b = jenkins_hash_int32(p->nocc);
  return jenkins_hash_pair(a, b, 0x32288cc9);
}

static uint32_t hash_bvc_mono64_hobj(bvc64_hobj_t *p) {
  uint32_t a, b;

  a = jenkins_hash_uint64(p->c);
  b = jenkins_hash_int32(p->nocc);
  return jenkins_hash_pair(a, b, 0xaef43e27);
}

static uint32_t hash_bvc_mono_hobj(bvc_hobj_t *p) {
  uint32_t a, b;

  a = bvconst_hash(p->c, p->bitsize);
  b = jenkins_hash_int32(p->nocc);
  return jenkins_hash_pair(a, b, 0xfe43a091);
}

// p->pp = array of len pairs of int32_t
static uint32_t hash_bvc_prod_hobj(bvc_prod_hobj_t *p) {
  assert(p->len <= UINT32_MAX/2);
  return jenkins_hash_intarray2((int32_t *) p->pp, 2 * p->len, 0x7432cde2);
}

static uint32_t hash_bvc_sum_hobj(bvc_sum_hobj_t *p) {
  return jenkins_hash_intarray2(p->noccs, p->len, 0xaeb32a06);
}


/*
 * Equality tests
 */
static bool eq_bvc_leaf_hobj(bvc_leaf_hobj_t *p, node_t i) {
  bvc_header_t *d;

  d = p->dag->desc[i];
  return d->tag == BVC_LEAF && leaf_node(d)->map == p->map;
}

static bool eq_bvc_offset64_hobj(bvc64_hobj_t *p, node_t i) {
  bvc_header_t *d;
  bvc_offset_t *o;

  d = p->dag->desc[i];
  if (d->tag != BVC_OFFSET || d->bitsize != p->bitsize) {
    return false;
  }
  o = offset_node(d);
  return o->nocc == p->nocc && o->constant.c == p->c;
}

static bool eq_bvc_offset_hobj(bvc_hobj_t *p, node_t i) {
  bvc_header_t *d;
  bvc_offset_t *o;
  uint32_t k;

  d = p->dag->desc[i];
  if (d->tag != BVC_OFFSET && d->bitsize != p->bitsize) {
    return false;
  }
  o = offset_node(d);
  k = (d->bitsize + 31) >> 5;
  return o->nocc == p->nocc && bvconst_eq(o->constant.w, p->c, k);
}

static bool eq_bvc_mono64_hobj(bvc64_hobj_t *p, node_t i) {
  bvc_header_t *d;
  bvc_mono_t *o;

  d = p->dag->desc[i];
  if (d->tag != BVC_MONO && d->bitsize != p->bitsize) {
    return false;
  } 
  o = mono_node(d);
  return o->nocc == p->nocc && o->coeff.c == p->c;
}

static bool eq_bvc_mono_hobj(bvc_hobj_t *p, node_t i) {
  bvc_header_t *d;
  bvc_mono_t *o;
  uint32_t k;

  d = p->dag->desc[i];
  if (d->tag != BVC_MONO || d->bitsize != p->bitsize) {
    return false;
  }
  o = mono_node(d);
  k = (d->bitsize + 31) >> 5;
  return o->nocc == p->nocc && bvconst_eq(o->coeff.w, p->c, k);
}

static bool eq_bvc_prod_hobj(bvc_prod_hobj_t *p, node_t i) {
  bvc_header_t *d;
  bvc_prod_t *o;
  uint32_t j, n;

  d = p->dag->desc[i];
  if (d->tag != BVC_PROD || d->bitsize != p->bitsize) {
    return false;
  }
  o = prod_node(d);
  n = o->len;
  if (n != p-> len) {
    return false;
  }

  for (j=0; j<n; j++) {
    if (p->pp[j].var != o->prod[j].var ||
	p->pp[j].exp != o->prod[j].exp) {
      return false;
    }
  }

  return true;
}

static bool eq_bvc_sum_hobj(bvc_sum_hobj_t *p, node_t i) {
  bvc_header_t *d;
  bvc_sum_t *o;
  uint32_t j, n;

  d = p->dag->desc[i];
  if (d->tag != BVC_SUM || d->bitsize != p->bitsize) {
    return false;
  }
  o = sum_node(d);
  n = o->len;
  if (n != p-> len) {
    return false;
  }

  for (j=0; j<n; j++) {
    if (p->noccs[j] != o->sum[j]) {
      return false;
    }
  }

  return true;
}


/*
 * Constructors
 */
static node_t build_bvc_leaf_hobj(bvc_leaf_hobj_t *p) {
  return bvc_dag_mk_leaf(p->dag, p->map, p->bitsize);
}

static node_t build_bvc_offset64_hobj(bvc64_hobj_t *p) {
  return bvc_dag_mk_offset64(p->dag, p->c, p->nocc, p->bitsize);
}

static node_t build_bvc_offset_hobj(bvc_hobj_t *p) {
  return bvc_dag_mk_offset(p->dag, p->c, p->nocc, p->bitsize);
}

static node_t build_bvc_mono64_hobj(bvc64_hobj_t *p) {
  return bvc_dag_mk_mono64(p->dag, p->c, p->nocc, p->bitsize);
}

static node_t build_bvc_mono_hobj(bvc_hobj_t *p) {
  return bvc_dag_mk_mono(p->dag, p->c, p->nocc, p->bitsize);
}

static node_t build_bvc_prod_hobj(bvc_prod_hobj_t *p) {
  return bvc_dag_mk_prod(p->dag, p->pp, p->len, p->bitsize);
}

static node_t build_bvc_sum_hobj(bvc_sum_hobj_t *p) {
  return bvc_dag_mk_sum(p->dag, p->noccs, p->len, p->bitsize);
}


/*
 * Hash-consing objects
 */
static bvc_leaf_hobj_t bvc_leaf_hobj = {
  { (hobj_hash_t) hash_bvc_leaf_hobj, (hobj_eq_t) eq_bvc_leaf_hobj, 
    (hobj_build_t) build_bvc_leaf_hobj },
  NULL, 0, 0
};

static bvc64_hobj_t bvc_offset64_hobj = {
  { (hobj_hash_t) hash_bvc_offset64_hobj, (hobj_eq_t) eq_bvc_offset64_hobj, 
    (hobj_build_t) build_bvc_offset64_hobj },
  NULL, 0, 0, 0
};

static bvc_hobj_t bvc_offset_hobj = {
  { (hobj_hash_t) hash_bvc_offset_hobj, (hobj_eq_t) eq_bvc_offset_hobj, 
    (hobj_build_t) build_bvc_offset_hobj },
  NULL, NULL, 0, 0  
};

static bvc64_hobj_t bvc_mono64_hobj = {
  { (hobj_hash_t) hash_bvc_mono64_hobj, (hobj_eq_t) eq_bvc_mono64_hobj, 
    (hobj_build_t) build_bvc_mono64_hobj },
  NULL, 0, 0, 0  
};

static bvc_hobj_t bvc_mono_hobj = {
  { (hobj_hash_t) hash_bvc_mono_hobj, (hobj_eq_t) eq_bvc_mono_hobj, 
    (hobj_build_t) build_bvc_mono_hobj },
  NULL, NULL, 0, 0  
};

static bvc_prod_hobj_t bvc_prod_hobj = {
  { (hobj_hash_t) hash_bvc_prod_hobj, (hobj_eq_t) eq_bvc_prod_hobj, 
    (hobj_build_t) build_bvc_prod_hobj },
  NULL, NULL, 0, 0,
};

static bvc_sum_hobj_t bvc_sum_hobj = {
  { (hobj_hash_t) hash_bvc_sum_hobj, (hobj_eq_t) eq_bvc_sum_hobj, 
    (hobj_build_t) build_bvc_sum_hobj },
  NULL, NULL, 0, 0,
};


/*
 * Hash-consing constructors
 */
static node_t bvc_dag_get_leaf(bvc_dag_t *dag, int32_t x, uint32_t bitsize) {
  bvc_leaf_hobj.dag = dag;
  bvc_leaf_hobj.bitsize = bitsize;
  bvc_leaf_hobj.map = x;
  return int_htbl_get_obj(&dag->htbl, &bvc_leaf_hobj.m);
}

static node_t bvc_dag_get_offset64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize) {
  bvc_offset64_hobj.dag = dag;
  bvc_offset64_hobj.c = a;
  bvc_offset64_hobj.bitsize = bitsize;
  bvc_offset64_hobj.nocc = n;
  return int_htbl_get_obj(&dag->htbl, &bvc_offset64_hobj.m);
}

static node_t bvc_dag_get_offset(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize) {
  bvc_offset_hobj.dag = dag;
  bvc_offset_hobj.c = a;
  bvc_offset_hobj.bitsize = bitsize;
  bvc_offset_hobj.nocc = n;
  return int_htbl_get_obj(&dag->htbl, &bvc_offset_hobj.m);
}

static node_t bvc_dag_get_mono64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize) {
  bvc_mono64_hobj.dag = dag;
  bvc_mono64_hobj.c = a;
  bvc_mono64_hobj.bitsize = bitsize;
  bvc_mono64_hobj.nocc = n;
  return int_htbl_get_obj(&dag->htbl, &bvc_mono64_hobj.m);
}

static node_t bvc_dag_get_mono(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize) {
  bvc_mono_hobj.dag = dag;
  bvc_mono_hobj.c = a;
  bvc_mono_hobj.bitsize = bitsize;
  bvc_mono_hobj.nocc = n;
  return int_htbl_get_obj(&dag->htbl, &bvc_mono_hobj.m);
}

// note: a must be sorted
static node_t bvc_dag_get_prod(bvc_dag_t *dag, varexp_t *a, uint32_t len, uint32_t bitsize) {
  bvc_prod_hobj.dag = dag;
  bvc_prod_hobj.pp = a;
  bvc_prod_hobj.bitsize = bitsize;
  bvc_prod_hobj.len = len;
  return int_htbl_get_obj(&dag->htbl, &bvc_prod_hobj.m);
}

// a must be sorted
static node_t bvc_dag_get_sum(bvc_dag_t *dag, node_occ_t *a, uint32_t len, uint32_t bitsize) {
  bvc_sum_hobj.dag = dag;
  bvc_sum_hobj.noccs = a;
  bvc_sum_hobj.bitsize = bitsize;
  bvc_sum_hobj.len = len;
  return int_htbl_get_obj(&dag->htbl, &bvc_sum_hobj.m);
}




/*
 * NORMALIZATION + NODE CONSTRUCTION
 */


/*
 * Store mapping [x --> n] in dag->vmap
 * - x must be positive
 * - n must be a valid node_occurrence in dag
 */
void bvc_dag_map_var(bvc_dag_t *dag, int32_t x, node_occ_t n) {
  int_hmap_pair_t *p;

  assert(x > 0 && !bvc_dag_var_is_present(dag, x));
  int_bvset_add(&dag->vset, x);
  p = int_hmap_get(&dag->vmap, x);
  assert(p->val == -1);
  p->val = n;
}



/*
 * Leaf node attached to variable x
 * - x must be positive
 */
node_occ_t bvc_dag_leaf(bvc_dag_t *dag, int32_t x, uint32_t bitsize) {
  assert(x > 0);
  return  bvp(bvc_dag_get_leaf(dag, x, bitsize));
}


/*
 * Get a node mapped to x
 * - if there's none, create the node [leaf x]
 */
node_occ_t bvc_dag_get_nocc_of_var(bvc_dag_t *dag, int32_t x, uint32_t bitsize) {
  assert(x > 0);

  if (bvc_dag_var_is_present(dag, x)) {
    return bvc_dag_nocc_of_var(dag, x);
  } else {
    return bvc_dag_leaf(dag, x, bitsize);
  }
}


/*
 * Construct an offset node q
 * - a must be normalized modulo 2^bitsize (and not be 0)
 */
node_occ_t bvc_dag_offset64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize) {
  assert(1 <= bitsize && bitsize <= 64 && a == norm64(a, bitsize) && a != 0);
  return bvp(bvc_dag_get_offset64(dag, a, n, bitsize));
}

node_occ_t bvc_dag_offset(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize) {
  assert(64 < bitsize && bvconst_is_normalized(a, bitsize));
  return bvp(bvc_dag_get_offset(dag, a, n, bitsize));
}




/*
 * Construct a monomial node q
 * - a must be normalized modulo 2^bitsize and must not be 0
 *
 * Depending on a and n, this gets turned into one of the following nodes:
 * - if a is +1  -->   n
 * - if a is -1  -->  -n
 * - otherwise,
 *   1) force n to positive sign
 *   2) depending on the number of '1' bits in a and -a,
 *      build either [mono a n] or [mono (-a) n]
 *
 * Heuristics:
 * - the number of adders required for (a * n) is equal to the number of '1'
 *   bits in a (i.e., to popcount(a)).
 * - (BVMUL a n) has cost equal to popcount(a)
 *   (BVNEG (BVMUL -a n)) has cost equal to  popcount(-a) + 1 (we count
 *    BVNEG as one more adder)
 *
 *
 * NOTE: there are better techniques
 * - could use a signed digit representation for the constant a
 * - if there are several monomials (a_0 x) ... (a_t x), then
 *   there are optimizations used in digital filter circuits:
 * 
 * Reference: 
 *  Dempster & McLeod, Constant integer multiplication using minimum adders, 
 *  IEE Proceedings, Cicuits, Devices & Systems, vol. 141, Issue 5, pp. 407-413,
 *  October 1994
 */
node_occ_t bvc_dag_mono64(bvc_dag_t *dag, uint64_t a, node_occ_t n, uint32_t bitsize) {
  uint64_t minus_a;
  uint32_t sign, ka, kma;
  node_t q;

  assert(1 <= bitsize && bitsize <= 64 && a == norm64(a, bitsize) && a != 0);

  if (a == 1) return n;
  if (a == mask64(bitsize)) return neg_occ(n);
    
  sign = sign_of_occ(n);
  n = unsigned_occ(n);

  /*
   * normalization: 
   * - is popcount(a)  < popcount(-a) then build [mono a n]
   * - if popcount(-a) < popcount(a)  then build [mono (-a) n]
   * - if there's a tie, we build [mono (-a) n] if -a is positive
   *                           or [mono a n] otherwise
   *
   * Note: if a is 0b10000...00 then both a and -a are negative and equal
   * so the tie-breaking rule works too (we want to build [mono a n]
   * in this case).
   */
  minus_a = norm64(-a, bitsize);
  ka = popcount64(a);
  kma = popcount64(minus_a);
  assert(1 <= ka && ka <= bitsize && 1 <= kma && kma <= bitsize);

  if (kma < ka || (kma == ka && is_pos64(minus_a, bitsize))) {
    a = minus_a;
    sign ^= 1; // flip the sign
  }

  q = bvc_dag_get_mono64(dag, a, n, bitsize);

  return  (q << 1) | sign;
}

node_occ_t bvc_dag_mono(bvc_dag_t *dag, uint32_t *a, node_occ_t n, uint32_t bitsize) {
  uint32_t *minus_a;
  uint32_t w, sign, ka, kma;
  node_t q;

  w = (bitsize + 31) >> 5; // number of words in a

  assert(64 < bitsize && bvconst_is_normalized(a, bitsize) && !bvconst_is_zero(a, w));

  if (bvconst_is_one(a, w)) return n;
  if (bvconst_is_minus_one(a, bitsize)) return neg_occ(n);

  sign = sign_of_occ(n);
  n = unsigned_occ(n);

  /*
   * Normalization: we store -a in dag->aux
   */
  bvconstant_copy(&dag->aux, bitsize, a);
  minus_a = dag->aux.data;
  bvconst_negate(minus_a, w);
  bvconst_normalize(minus_a, bitsize);

  ka = bvconst_popcount(a, w);
  kma = bvconst_popcount(minus_a, w);
  assert(1 <= ka && ka <= bitsize && 1 <= kma && kma <= bitsize);

  if (kma < ka || (kma == ka && !bvconst_tst_bit(minus_a, bitsize - 1))) {
    a = minus_a;
    sign ^= 1; // flip the sign
  }

  q = bvc_dag_get_mono(dag, a, n, bitsize);
  return (q << 1) | sign;
}



/*
 * Construct a sum node q
 * - a = array of n node occurrences
 * - n must be positive
 *
 * If n == 1, this returns a[0].
 * Otherwise, a is sorted and a node q := [sum a[0] ... a[n-1]] is created
 */
node_occ_t bvc_dag_sum(bvc_dag_t *dag, node_occ_t *a, uint32_t n, uint32_t bitsize) {
  assert(n > 0);

  if (n == 1) return a[0];

  int_array_sort(a, n);
  return bvp(bvc_dag_get_sum(dag, a, n, bitsize));
}



/*
 * Construct a product node q
 * - q is defined by the exponents in power product p and the
 *   nodes in array a: if p is x_1^d_1 ... x_k^d_k
 *   then a must have k elements a[0] ... a[k-1]
 *   and q is [prod a[0]^d_1 ... a[k-1]^d_k]
 */
node_occ_t bvc_dag_pprod(bvc_dag_t *dag, pprod_t *p, node_occ_t *a, uint32_t bitsize) {
  pp_buffer_t *buffer;
  uint32_t i, n;

  // build the power product in dag->pp_aux
  buffer = &dag->pp_aux;
  pp_buffer_reset(buffer);
  n = p->len;
  for (i=0; i<n; i++) {
    pp_buffer_mul_varexp(buffer, a[i], p->prod[i].exp);
  }
  
  return bvp(bvc_dag_get_prod(dag, buffer->prod, buffer->len, bitsize));
}



/*
 * Convert a polynomial p to a DAG node q and return q
 * - q is defined by the coefficients in p and the node indices
 *   in array a: if p is b_0 x_0 + b_1 x_1 + ... + b_k x_k 
 *   then a must have k+1 elements a[0] ... a[k]
 *   and q is built for (b_0 * a[0] + b_1 a[1] + ... + b_k a[k])
 *
 * - if x_0 is const_idx, then a[0] is ignored and 
 *       q is built for (b_0 + b_1 a[1] + ... + b_k a[k]).
 *
 * The DAG for p = (b0 + b_1 a[1] + .... + b_k a[k]) is 
 *    [offset b0 [sum [mono b_1 a[1]] ... [mono b_k a[k]]]].
 */
node_occ_t bvc_dag_poly64(bvc_dag_t *dag, bvpoly64_t *p, node_occ_t *a) {
  ivector_t *v;
  uint32_t i, n, bitsize;
  node_occ_t r;

  n = p->nterms;
  bitsize = p->bitsize;
  i = 0;
  if (p->mono[0].var == const_idx) {
    // skip the constant
    i = 1;
  }

  // build the monomials and store the corresponding node occs in v
  v = &dag->buffer;
  assert(v->size == 0);

  while (i < n) {
    r = bvc_dag_mono64(dag, p->mono[i].coeff, a[i], bitsize);
    ivector_push(v, r);
    i ++;
  }
  ivector_reset(v);

  // build the sum
  r = bvc_dag_sum(dag, v->data, v->size, bitsize);

  // add the constant if any
  if (p->mono[0].var == const_idx) {
    r = bvc_dag_offset64(dag, p->mono[0].coeff, r, bitsize);
  }

  return r;
}

node_occ_t bvc_dag_poly(bvc_dag_t *dag, bvpoly_t *p, node_occ_t *a) {
  ivector_t *v;
  uint32_t i, n, bitsize;
  node_occ_t r;

  n = p->nterms;
  bitsize = p->bitsize;
  i = 0;
  if (p->mono[0].var == const_idx) {
    // skip the constant
    i = 1;
  }

  // build the monomials and store the corresponding node occs in v
  v = &dag->buffer;
  assert(v->size == 0);

  while (i < n) {
    r = bvc_dag_mono(dag, p->mono[i].coeff, a[i], bitsize);
    ivector_push(v, r);
    i ++;
  }
  ivector_reset(v);

  // build the sum
  r = bvc_dag_sum(dag, v->data, v->size, bitsize);

  // add the constant if any
  if (p->mono[0].var == const_idx) {
    r = bvc_dag_offset(dag, p->mono[0].coeff, r, bitsize);
  }

  return r;  
}

