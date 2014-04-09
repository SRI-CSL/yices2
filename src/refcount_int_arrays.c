/*
 * Integer arrays with reference counters
 */

#include <assert.h>

#include "memalloc.h"
#include "refcount_int_arrays.h"


/*
 * Allocate an array of n elements
 * - set ref counter to zero
 */
int32_t *alloc_int_array(uint32_t n) {
  int_array_t *tmp;

  if (n > MAX_REFCOUNT_INT_ARRAY_SIZE) {
    out_of_memory();
  }

  tmp = (int_array_t *) safe_malloc(sizeof(int_array_t) + n * sizeof(int32_t));
  tmp->ref = 0;
  return tmp->data;
}


/*
 * Decrement the reference counter for a
 * - if the counter reaches zero, delete a
 */
void int_array_decref(int32_t *a) {
  int_array_t *h;

  if (a != NULL) {
    h = int_array_header(a);
    assert(h->ref > 0);
    h->ref --;
    if (h->ref == 0) free(h);
  }
}
