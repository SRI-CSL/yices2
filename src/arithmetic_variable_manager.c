/*
 * Manager for arithmetic variables: use polynomial_manager
 * additional field: i_flag = bit vector
 * m->i_flag[i] = 1 if i is an integer variable
 * m->i_flag[i] = 0 otherwise.
 */

#include "memalloc.h"
#include "arithmetic_variable_manager.h"


/*
 * Check whether all the variables in a product are integer
 */
static bool is_integer_product(arithvar_manager_t *m, varexp_t *p, int32_t n) {
  int32_t i;

  for (i=0; i<n; i++) {
    if (! tst_bit(m->i_flag, p[i].var)) return false;
  }
  return true;
}

static inline bool is_integer_varprod(arithvar_manager_t *m, varprod_t *p) {
  return is_integer_product(m, p->prod, p->len);
}

static inline bool is_integer_vpbuffer(arithvar_manager_t *m, vpbuffer_t *b) {
  return is_integer_product(m, b->prod, b->len);
}


/*
 * Resize notifier: extend the i_flag vector
 */
static void arithvar_resize_notify(void *m, uint32_t old_size, uint32_t new_size) {
  arithvar_manager_t *manager;

  manager = (arithvar_manager_t *) m;
  manager->i_flag = extend_bitvector(manager->i_flag, new_size);
}

/*
 * New prod notifier: set the i_flag bit
 */
static void arithvar_newprod_notify(void *m, int32_t new_index, varprod_t *p) {
  arithvar_manager_t *manager;
  bool is_int;

  manager = (arithvar_manager_t *) m;
  is_int = is_integer_varprod(manager, p);
  assign_bit(manager->i_flag, new_index, is_int);
}



/*
 * Initialize and store the constant idx = empty product.
 * n = initial size.
 */
void init_arithvar_manager(arithvar_manager_t *m, uint32_t n) {
  init_polymanager(&m->pm, n);
  assert(m->pm.size >= n && m->pm.size > 0);

  n = m->pm.size; // in case polymanager_init caused a resize.
  m->i_flag = allocate_bitvector(n);

  // set i_flag for empty product
  set_bit(m->i_flag, const_idx);

  polymanager_set_resize_notifier(&m->pm, arithvar_resize_notify);
  polymanager_set_newprod_notifier(&m->pm, arithvar_newprod_notify);
}


/*
 * Add new var and return its index.
 * - is_int true means the variable is integer 
 */
int32_t arithvar_manager_new_var(arithvar_manager_t *m, bool is_int, int32_t term_id) {
  int32_t i;

  i = polymanager_new_var(&m->pm, term_id);
  assign_bit(m->i_flag, i, is_int);

  return i;
}


/*
 * Free memory
 */
void delete_arithvar_manager(arithvar_manager_t *m) {
  delete_bitvector(m->i_flag);
  delete_polymanager(&m->pm);
  m->i_flag = NULL;
}

