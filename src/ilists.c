/*
 * Lists of integers
 */

#include "ilists.h"


/*
 * Initialize an object store for these elements
 * - the store must be passed to all list operations
 */
void init_ilist_store(object_store_t *store) {
  init_objstore(store, sizeof(ilist_t), 4096);
}



/*
 * Cons: insert x has head of the list
 */
ilist_t *ilist_cons(object_store_t *store, int32_t x, ilist_t *l) {
  ilist_t *aux;

  aux = objstore_alloc(store);
  aux->next = l;
  aux->elem = x;

  return aux;
}


/*
 * Add a[0 ... n-1] to list l
 */
ilist_t *ilist_cons_array(object_store_t *store, uint32_t n, int32_t *a, ilist_t *l) {
  while (n > 0) {
    n --;
    l = ilist_cons(store, a[n], l);
  }
  return l;
}


/*
 * Make a copy of l in reverse order
 */
ilist_t *ilist_reverse_clone(object_store_t *store, ilist_t *l) {
  ilist_t *aux;

  aux = NULL;
  while (l != NULL) {
    aux = ilist_cons(store, l->elem, aux);
    l = l->next;
  }
  return aux;
}


/*
 * Append l1 and l2: l1 is first
 */
ilist_t *ilist_append(object_store_t *store, ilist_t *l1, ilist_t *l2) {
  ilist_t *r1, *r2;
  
  r1 = ilist_reverse_clone(store, l1);
  while (r1 != NULL) {
    r2 = r1->next;
    r1->next = l2;
    l2 = r1;
    r1 = r2;
  }

  return l2;
}



/*
 * Length of l
 */
uint32_t ilist_length(const ilist_t *l) {
  uint32_t len;

  len = 0;
  while (l != NULL) {
    len ++;
    l = l->next;
  }

  return len;
}


/*
 * Collect the elements of l into vector v
 * - this adds all elements of l in order, at the end of v
 * - v is not reset 
 */
void ilist_collect(const ilist_t *l, ivector_t *v) {
  while (l != NULL) {
    ivector_push(v, l->elem);
    l = l->next;
  }
}

