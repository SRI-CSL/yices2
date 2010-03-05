/*
 * Manager for bitvector variables: polynomial manager
 * with extra fields:
 * m->bitsize[i] = number of bits in variable i
 * m->bit[i] = array of bit expressions attached to i (or NULL)
 */

#include <assert.h>

#include "memalloc.h"
#include "bitvector_variable_manager.h"


/*
 * Bitsize of product p
 */
static uint32_t bitsize_varprod(bv_var_manager_t *m, varprod_t *p) {
#ifndef NDEBUG
  // Check that the product is well formed
  int32_t i, n;
  uint32_t s;
  varexp_t *a;

  n = p->len;
  if (n > 0) {
    a = p->prod;
    s = m->bitsize[a[0].var];
    for (i=0; i<n; i++) {
      assert(m->bitsize[a[i].var] == s);
    }
  }
#endif

  if (p->len == 0) {
    return 0;
  } else {
    return m->bitsize[p->prod[0].var];
  }
}


/*
 * Resize notifier: extend bitsize and bit vectors
 */
static void bv_var_resize_notify(void *m, uint32_t old_size, uint32_t new_size) {
  bv_var_manager_t *manager;

  manager = (bv_var_manager_t *) m;
  manager->bitsize = (uint32_t *) safe_realloc(manager->bitsize, new_size * sizeof(uint32_t));
  manager->bit = (bit_t **) safe_realloc(manager->bit, new_size * sizeof(bit_t *));
}

/*
 * New prod notifier: set the size and initialize bit[i] to NULL
 */
static void bv_var_newprod_notify(void *m, int32_t new_index, varprod_t *p) {
  bv_var_manager_t *manager;

  manager = (bv_var_manager_t *) m;
  manager->bitsize[new_index] = bitsize_varprod(manager, p);
  manager->bit[new_index] = NULL;
}



/*
 * Initialize and store the constant idx = empty product.
 * - n = initial size.
 * - node_table = attached table of bit expressions
 */
void init_bv_var_manager(bv_var_manager_t *m, uint32_t n, node_table_t *node_table) {
  init_polymanager(&m->pm, n);
  assert(m->pm.size >= n && m->pm.size > 0);

  n = m->pm.size; // polymanager_init may have caused a resize.
  m->bitsize = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  m->bit = (bit_t **) safe_malloc(n * sizeof(bit_t *));
  m->bm = node_table;

  // set bitsize and array for const_idx
  m->bitsize[const_idx] = 0;
  m->bit[const_idx] = NULL;

  polymanager_set_resize_notifier(&m->pm, bv_var_resize_notify);
  polymanager_set_newprod_notifier(&m->pm, bv_var_newprod_notify);
}


/*
 * Free memory
 */
void delete_bv_var_manager(bv_var_manager_t *m) {
  int32_t i, n;

  n = m->pm.nelems; 
  // delete the bit arrays and variables
  for (i=0; i<n; i++) {
    safe_free(m->bit[i]);
  }
  safe_free(m->bitsize);
  safe_free(m->bit);
  delete_polymanager(&m->pm);
  m->bitsize = NULL;
  m->bit = NULL;
}



/*
 * Add new var of given size and return its index.
 */
int32_t bv_var_manager_new_var(bv_var_manager_t *m, uint32_t size, int32_t term_id) {
  int32_t i;

  i = polymanager_new_var(&m->pm, term_id);
  m->bitsize[i] = size;
  m->bit[i] = NULL;

  return i;
}

/*
 * Delete variable v
 */
void bv_var_manager_delete_var(bv_var_manager_t *m, int32_t v) {
  bit_t *b;

  polymanager_delete_var(&m->pm, v);

  /*
   * delete the attached bit array 
   * NOTE: the nodes in the bit array must be deleted via the node
   * table garbage collector (so we don't delete them here).
   */
  b = m->bit[v];
  if (b != NULL) {
    safe_free(b);
    m->bit[v] = NULL;
  }
  
}


/*
 * Return the bdd array attached to v.
 * If bit[v] = NULL, declare n variables in the bdd manager,
 * and create n variable nodes in the node table.
 */
bit_t *bv_var_manager_get_bit_array(bv_var_manager_t *m, int32_t v) {
  bit_t *b;
  uint32_t n, i;

  b = m->bit[v];
  if (b == NULL) {
    n = m->bitsize[v];
    b = (bit_t *) safe_malloc(n * sizeof(bit_t));
    for (i=0; i<n; i++) {
      b[i] = node_table_alloc_var(m->bm, v);
    }
    m->bit[v] = b;
  }

  return b;
}



/*
 * Return the index of bit-expression bit in the array attached to variable v
 * - v must be a valid variable
 * - return -1 if bit does not occur in the array (or if v has no array attached)
 */
int32_t bv_var_manager_get_index_of_node(bv_var_manager_t *m, int32_t v, node_t bit) {
  bit_t *b;
  uint32_t i, n;

  b = bv_var_bit_array(m, v);
  if (b != NULL) {
    n = m->bitsize[v];
    for (i=0; i<n; i++) {
      if (b[i] == bit) {
	return i;
      }
    }
  }

  return -1;
}

