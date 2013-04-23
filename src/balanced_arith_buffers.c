/*
 * BUFFER FOR ARITHMETIC OPERATIONS USING RED-BLACK TREES
 */

#include "memalloc.h"
#include "balanced_arith_buffers.h"


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
  b->node = (rb_node_t *) safe_malloc(n * sizeof(rb_node_t));
  b->isred = allocate_bitvector(n);

  b->ptbl = ptbl;
  init_ivector(&b->stack, 20);

  assert(n > 0 && rba_null == 0);
  
  // initialize the null node
  b->mono[0].prod = NULL;
  q_init(&b->mono[0].coeff);
  b->node[0][0] = 0;
  b->node[0][1] = 1;
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
  b->node = (rb_node_t *) safe_realloc(b->node, n * sizeof(rb_node_t));
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
    b->free_list = b->node[i][0];
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
  b->node[i][0] = b->free_list;
  b->free_list = i;
}


/*
 * Free memory
 */
void delete_rba_buffer(rba_buffer_t *b) {
  uint32_t i, n;

  n = b->num_nodes;
  for (i=0; i<n; i++) {
    clear_rba_mono(b->mono + i);
  }
  safe_free(b->mono);
  safe_free(b->node);
  delete_bitvector(b->isred);
  delete_ivector(&b->stack);
  b->mono = NULL;
  b->node = NULL;
  b->isred = NULL;
}



/*
 * Reset b to the empty tree
 */
void reset_rba_buffer(rba_buffer_t *b) {
  // TBD
}





/*
 * Convert b to a polynomial then reset b
 * - v = array of variables
 */
