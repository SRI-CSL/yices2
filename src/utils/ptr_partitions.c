/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Data structure to collect classes of objects. This is intended
 * to be used to construct the classes that contain at least two objects.
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/ptr_partitions.h"


/*
 * Add pointer *p to vector *v
 * - if *v is NULL, allocate a new vector of default size
 * - if *v is full, resize it
 */
static void ppart_push(void ***v, void *p) {
  ppart_vector_t *u;
  void **a;
  uint32_t i, n;

  a = *v;
  if (a == NULL) {
    // allocate a new vector
    i = 0;
    n = DEF_PPART_VSIZE;
    assert(n <= MAX_PPART_VSIZE);
    u = (ppart_vector_t *) safe_malloc(sizeof(ppart_vector_t) + n * sizeof(void *));
    u->capacity = n;
    a = u->data;
    *v = a;
  } else {
    u = ppv_header(a);
    i = u->size;
    n = u->capacity;
    if (i == n) {
      // make the vector 50% larger
      n ++;
      n += n>>1;
      if (n > MAX_PPART_VSIZE) {
        out_of_memory();
      }
      u = (ppart_vector_t *) safe_realloc(u, sizeof(ppart_vector_t) + n * sizeof(void *));
      u->capacity = n;
      a = u->data;
      *v = a;
    }
  }

  assert(i < u->capacity && a == u->data);
  a[i] = p;
  u->size = i+1;
}


/*
 * Delete vector v (must be non-NULL)
 */
static void ppart_delete_vector(void **v) {
  ppart_vector_t *u;

  assert(v != NULL);
  u = ppv_header(v);
  safe_free(u);
}



/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (- n)) == n;
}
#endif


/*
 * Initialize pp
 * - n = hash table size:
 *   n must be a power of 2. If n=0, the default size is used.
 * - hash_fn, match_fn, aux: customization
 * - the table is empty, classes is not allocated yet (NULL).
 */
void init_ptr_partition(ppart_t *pp, uint32_t n, void *aux, ppart_hash_fun_t hash_fn, ppart_match_fun_t match_fn) {
  ppart_rec_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_PPART_SIZE;
  }

  assert(is_power_of_two(n));

  if (n >= MAX_PPART_SIZE) {
    out_of_memory();
  }

  // Initialize: empty hash table of size n
  tmp = (ppart_rec_t *) safe_malloc(n * sizeof(ppart_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].data = NULL;
  }

  pp->records = tmp;
  pp->classes = NULL;
  pp->size = n;
  pp->nelems = 0;
  pp->resize_threshold = (uint32_t)(n * PPART_RESIZE_RATIO);
  pp->csize = 0;
  pp->nclasses = 0;
  pp->aux = aux;
  pp->hash = hash_fn;
  pp->match = match_fn;
}


/*
 * Delete: free all memory
 */
void delete_ptr_partition(ppart_t *pp) {
  uint32_t i, n;

  n = pp->nclasses;
  for (i=0; i<n; i++) {
    ppart_delete_vector(pp->classes[i]);
  }
  safe_free(pp->classes);
  pp->classes = NULL;

  safe_free(pp->records);
  pp->records = NULL;
}




/*
 * Reset: empty the table
 * - remove all classes
 * - remove all elements in the hash table.
 */
void reset_ptr_partition(ppart_t *pp) {
  uint32_t i, n;

  n = pp->nclasses;
  for (i=0; i<n; i++) {
    ppart_delete_vector(pp->classes[i]);
  }
  pp->nclasses = 0;

  n = pp->size;
  for (i=0; i<n; i++) {
    pp->records[i].data = NULL;
  }
  pp->nelems = 0;
}



/*
 * Copy record r into array a
 * - mask = size of a - 1
 * - size of a must be a power of two
 * - a must not be full
 */
static void ppart_copy_record(ppart_rec_t *a, ppart_rec_t *r, uint32_t mask) {
  uint32_t i;

  assert(r->data != NULL);
  i = r->hash & mask;
  while (a[i].data != NULL) {
    i ++;
    i &= mask;
  }
  a[i] = *r;
}



/*
 * Resize the hash table: double the size, keep the content
 */
static void resize_ptr_partition(ppart_t *pp) {
  ppart_rec_t *tmp, *r;
  uint32_t i, n, n2, mask;

  n = pp->size;
  n2 = n << 1;
  if (n2 >= MAX_PPART_SIZE) {
    out_of_memory();
  }

  tmp = (ppart_rec_t *) safe_malloc(n2 * sizeof(ppart_rec_t));
  for (i=0; i<n2; i++) {
    tmp[i].data = NULL;
  }

  // copy current content into tmp
  mask = n2 - 1;
  r = pp->records;
  for (i=0; i<n; i++) {
    if (r->data != NULL) {
      ppart_copy_record(tmp, r, mask);
    }
    r ++;
  }

  // cleanup
  safe_free(pp->records);
  pp->records = tmp;
  pp->size = n2;
  pp->resize_threshold = (uint32_t) (n2 * PPART_RESIZE_RATIO);
}



/*
 * Allocate a new class: return it's id
 * - the new class vector is pp->classes[i]. It's initialized to NULL
 */
static uint32_t allocate_class(ppart_t *pp) {
  uint32_t i, n;

  n = pp->csize;
  i = pp->nclasses;
  if (i == n) {
    // allocate or resize the classes array
    if (n == 0) {
      n = DEF_PPART_CSIZE;
      assert(n <= MAX_PPART_CSIZE);
    } else {
      n ++;
      n += n>>1; // 50% larger
      if (n > MAX_PPART_CSIZE) {
        out_of_memory();
      }
    }

    pp->classes = (void ***) safe_realloc(pp->classes, n * sizeof(void **));
    pp->csize = n;
  }

  assert(i < pp->csize && pp->classes != NULL);
  pp->classes[i] = NULL;
  pp->nclasses = i+1;

  return i;
}


/*
 * Add ptr to the table:
 * - if there's a pointer p in the table that matches ptr
 *   then ptr is added to p's class. If p has no class attached
 *   yet, then a new class vector is allocated and both p and
 *   ptr are added to that class.
 */
void ptr_partition_add(ppart_t *pp, void *ptr) {
  uint32_t mask, h, j;
  int32_t i;
  ppart_rec_t *r;

  assert(pp->nelems < pp->size);

  mask = pp->size - 1;
  h = pp->hash(pp->aux, ptr);  // hash code for ptr
  j = h & mask;
  for (;;) {
    r = pp->records + j;

    if (r->data == NULL) {
      // empty record found: ptr starts a new class
      r->hash = h;
      r->cid = -1; // no class attached yet
      r->data = ptr;
      pp->nelems ++;
      if (pp->nelems > pp->resize_threshold) {
        resize_ptr_partition(pp);
      }
      return;
    }

    if (r->hash == h && pp->match(pp->aux, ptr, r->data)) {
      // match found: add ptr to r's class
      i = r->cid;
      if (i < 0) {
        i = allocate_class(pp);
        r->cid = i;
        ppart_push(pp->classes + i, r->data);
      }
      ppart_push(pp->classes + i, ptr);
      return;
    }

    j ++;
    j &= mask;
  }

}



/*
 * Find the class index of ptr
 * - return the index of the vector that contains ptr
 * - return -1 if there's no such vector
 */
int32_t ptr_partition_get_index(ppart_t *pp, void *ptr) {
  uint32_t mask, h, j;
  ppart_rec_t *r;

  assert(pp->nelems < pp->size);

  mask = pp->size - 1;
  h = pp->hash(pp->aux, ptr);
  j = h & mask;
  for (;;) {
    r = pp->records + j;
    if (r->data == NULL) return -1;
    if (r->hash == h && pp->match(pp->aux, ptr, r->data)) return r->cid;
    j ++;
    j &= mask;
  }
}
