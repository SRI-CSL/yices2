#include <assert.h>
#include <stdbool.h>

#include "indexed_table.h"
#include "memalloc.h"
#include "yices_limits.h"

static inline size_t elem_size(const indexed_table_t *t) {
  return t->vtbl->elem_size;
}

static inline void check_nelems(const indexed_table_t *t) {
  if (t->size > t->vtbl->max_elems)
    out_of_memory();
}

static inline indexed_table_elem_t *elem(indexed_table_t *t, index_t i) {
  return (indexed_table_elem_t *) (((char *) t->elems) + i * elem_size(t));
}

static void extend(indexed_table_t *t) {
  uindex_t n;
    
  n = t->size + 1;
  n += n >> 1;
  t->size = n;
  check_nelems(t);

  t->elems = safe_realloc(t->elems, n * elem_size(t));

  if (t->vtbl->extend)
    t->vtbl->extend(t);
}

void indexed_table_init(indexed_table_t *t, uindex_t n,
			const indexed_table_vtbl_t *vtbl) {
  *t = (indexed_table_t) {
    .elems = safe_malloc(n * vtbl->elem_size),
    .size = n,
    .vtbl = vtbl
  };
  check_nelems(t);

  indexed_table_clear(t);
}

void indexed_table_destroy(indexed_table_t *t) {
  safe_free(t->elems);
}

index_t indexed_table_alloc(indexed_table_t *t) {
  index_t i = t->free_idx;

  if (i >= 0) {
    t->free_idx = elem(t, i)->next;
  } else {
    i = t->nelems++;
    if (i == t->size)
      extend(t);
    assert(i < t->size);
  }

  t->live_elems++;

  return i;
}

void indexed_table_free(indexed_table_t *t, index_t i) {
  elem(t, i)->next = t->free_idx;
  t->free_idx = i;

  t->live_elems--;
}

void indexed_table_clear(indexed_table_t *t) {
  t->nelems = 0;
  t->free_idx = -1;
  t->live_elems = 0;
}

void indexed_table_for_each_free_elem(indexed_table_t *t,
				      indexed_table_elem_fn f,
				      void *data) {
  index_t i, next;

  for (i = t->free_idx; i >= 0; i = next) {
    indexed_table_elem_t *e = elem(t, i);

    /* Obtain the next index before calling F in case F mutates the
       element. */
    next = e->next;

    f(e, i, data);
  }
}
