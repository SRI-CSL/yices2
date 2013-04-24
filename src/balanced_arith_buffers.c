/*
 * BUFFER FOR ARITHMETIC OPERATIONS USING RED-BLACK TREES
 */

#include "bit_tricks.h"
#include "memalloc.h"
#include "balanced_arith_buffers.h"


/*
 * When performing some operation f on the monomials stored in b, we
 * can either do a linear scan
 *
 *    for (i=0; i<b->num_nodes; i++) {
 *      f(b->mono + i)
 *    }
 * 
 * or we can traverse the tree using a recursive function.
 *
 * Linear scan has a cost of linear in num_nodes.
 *
 * Tree traversal has cost K * nterms * log(nterms) (approximately)
 * for some constant K>1.
 *
 * In most cases, the linear scan should be faster. But the recursive
 * scan will be faster if num_terms is really small compared to 
 * num_nodes. The following function is a heuristic that attempts to
 * determine when tree traversal is cheaper than linear scan.
 */
static bool rba_tree_is_small(rba_buffer_t *b) {
  uint32_t n, p;

  n = b->nterms;
  p = b->num_nodes;
  return n * binlog(n) < (p >> 3);
}



/*
 * Initialize and finalize a monomial
 */
static inline void init_rba_mono(mono_t *m) {
  q_init(&m->coeff);
}

static inline void clear_rba_mono(mono_t *m) {
  q_clear(&m->coeff);
}




/*
 * Inialize buffer
 */
void init_rba_buffer(rba_buffer_t *b, pprod_table_t *ptbl) {
  uint32_t n;

  n = DEF_RBA_BUFFER_SIZE;
  assert(n <= MAX_RBA_BUFFER_SIZE);

  b->mono = (mono_t *) safe_malloc(n * sizeof(mono_t));
  b->child = (rb_node_t *) safe_malloc(n * sizeof(rb_node_t));
  b->isred = allocate_bitvector(n);

  b->ptbl = ptbl;
  init_ivector(&b->stack, 20);

  assert(n > 0 && rba_null == 0);
  
  // initialize the null node
  b->mono[0].prod = NULL;
  q_init(&b->mono[0].coeff);
  b->child[0][0] = 0;
  b->child[0][1] = 1;
  clr_bit(b->isred, 0); // null node must be black

  b->size = n;
  b->num_nodes = 1;
  b->nterms = 0;
  b->root = 0;      // rba_null
  b->free_list = 0; // also rba_null (empty list)
}


/*
 * Extend: increase size by 50%
 */
static void extend_rba_buffer(rba_buffer_t *b) {
  uint32_t n;

  n = b->size + 1;
  n += (n >> 1);
  if (n > MAX_RBA_BUFFER_SIZE) {
    out_of_memory();
  }

  b->mono = (mono_t *) safe_realloc(b->mono, n * sizeof(mono_t));
  b->child = (rb_node_t *) safe_realloc(b->child, n * sizeof(rb_node_t));
  b->isred = extend_bitvector(b->isred, n);
  b->size = n;
}


/*
 * Allocate a node: return its id
 */
static uint32_t rba_alloc_node(rba_buffer_t *b) {
  uint32_t i;

  i = b->free_list;
  if (i != rba_null) {
    b->free_list = b->child[i][0];
  } else {
    i = b->num_nodes;
    if (i == b->size) {
      extend_rba_buffer(b);
    }
    assert(i < b->size);
    init_rba_mono(b->mono + i);
    b->num_nodes = i+1;
  }

  assert(0 < i && i < b->num_nodes);

  return i;
}


/*
 * Free node i: add it to the free list
 */
static void rba_free_node(rba_buffer_t *b, uint32_t i) {
  assert(0 < i && i < b->num_nodes);
  b->child[i][0] = b->free_list;
  b->free_list = i;
}



/*
 * Scan tree and finalize all monomials
 * - if the tree is small, we traverse the tree
 * - otherwise, we use a linear scan of b->mono
 */
// recursive version: cleanup all monomials reachable from node i
static void cleanup_tree(rba_buffer_t *b, uint32_t i) {
  assert(0 <= i && i < b->num_nodes);
  if (i != rba_null) {
    clear_rba_mono(b->mono + i);
    cleanup_tree(b, b->child[i][0]);
    cleanup_tree(b, b->child[i][1]);
  }		     
}

static void rba_cleanup(rba_buffer_t *b) {
  uint32_t i, n;

  if (rba_tree_is_small(b)) {
    cleanup_tree(b, b->root);
  } else {
    n = b->num_nodes;
    for (i=0; i<n; i++) {
      clear_rba_mono(b->mono + i);
    }
  }
}


/*
 * Free memory
 */
void delete_rba_buffer(rba_buffer_t *b) {
  rba_cleanup(b);
  safe_free(b->mono);
  safe_free(b->child);
  delete_bitvector(b->isred);
  delete_ivector(&b->stack);
  b->mono = NULL;
  b->child = NULL;
  b->isred = NULL;
}



/*
 * Reset b to the empty tree
 */
void reset_rba_buffer(rba_buffer_t *b) {
  rba_cleanup(b);
  b->num_nodes = 1;
  b->nterms = 0;
  b->root = 0;
  b->free_list = 0;
}





/*
 * Convert b to a polynomial then reset b
 * - v = array of variables
 */
