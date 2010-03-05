/*
 * Data structure to collect classes of objects. This is intended
 * to be used to construct the classes that contain at least two objects.
 * (objects are identified by an integer index).
 */

#include <assert.h>

#include "memalloc.h"
#include "int_partitions.h"


/*
 * Add index x to vector *v
 * - if *v is NULL, allocate a new vector of default size
 * - if *v is full, resize it
 */
static void ipart_push(int32_t **v, int32_t x) {
  ipart_vector_t *u;
  int32_t *a;
  uint32_t i, n;

  a = *v;
  if (a == NULL) {
    // allocate a new vector
    i = 0;
    n = DEF_IPART_VSIZE;
    assert(n <= MAX_IPART_VSIZE);
    u = (ipart_vector_t *) safe_malloc(sizeof(ipart_vector_t) + n * sizeof(int32_t));
    u->capacity = n;
    a = u->data;
    *v = a;
  } else {
    u = ipv_header(a);
    i = u->size;
    n = u->capacity;
    if (i == n) {
      // make the vector 50% larger
      n ++;
      n += n>>1;
      if (n > MAX_IPART_VSIZE) {
	out_of_memory();
      }
      u = (ipart_vector_t *) safe_realloc(u, sizeof(ipart_vector_t) + n * sizeof(int32_t));
      u->capacity = n;
      a = u->data;
      *v = a;
    }
  }

  assert(i < u->capacity && a == u->data);
  a[i] = x;
  u->size = i+1;
}


/*
 * Delete vector v (must be non-NULL)
 */
static void ipart_delete_vector(int32_t *v) {
  ipart_vector_t *u;

  assert(v != NULL);
  u = ipv_header(v);
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
void init_int_partition(ipart_t *pp, uint32_t n, void *aux, ipart_hash_fun_t hash_fn, ipart_match_fun_t match_fn) {
  ipart_rec_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_IPART_SIZE;
  }

  assert(is_power_of_two(n));

  if (n >= MAX_IPART_SIZE) {
    out_of_memory();
  }

  // Initialize: empty hash table of size n
  tmp = (ipart_rec_t *) safe_malloc(n * sizeof(ipart_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].data = null_index;
  }

  pp->records = tmp;
  pp->classes = NULL;
  pp->size = n;
  pp->nelems = 0;
  pp->resize_threshold = (uint32_t)(n * IPART_RESIZE_RATIO);
  pp->csize = 0;
  pp->nclasses = 0;
  pp->aux = aux;
  pp->hash = hash_fn;
  pp->match = match_fn;
}


/*
 * Delete: free all memory
 */
void delete_int_partition(ipart_t *pp) {
  uint32_t i, n;

  n = pp->nclasses;
  for (i=0; i<n; i++) {
    ipart_delete_vector(pp->classes[i]);
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
void reset_int_partition(ipart_t *pp) {
  uint32_t i, n;

  n = pp->nclasses;
  for (i=0; i<n; i++) {
    ipart_delete_vector(pp->classes[i]);
  }
  pp->nclasses = 0;

  n = pp->size;
  for (i=0; i<n; i++) {
    pp->records[i].data = null_index;
  }
  pp->nelems = 0;  
}



/*
 * Copy record r into array a
 * - mask = size of a - 1
 * - size of a must be a power of two
 * - a must not be full
 */
static void ipart_copy_record(ipart_rec_t *a, ipart_rec_t *r, uint32_t mask) {
  uint32_t i;

  assert(r->data != null_index);
  i = r->hash & mask;
  while (a[i].data != null_index) {
    i ++;
    i &= mask;
  }
  a[i] = *r;
}



/*
 * Resize the hash table: double the size, keep the content
 */
static void resize_int_partition(ipart_t *pp) {
  ipart_rec_t *tmp, *r;
  uint32_t i, n, n2, mask;

  n = pp->size;
  n2 = n << 1;
  if (n2 >= MAX_IPART_SIZE) {
    out_of_memory();
  }

  tmp = (ipart_rec_t *) safe_malloc(n2 * sizeof(ipart_rec_t));
  for (i=0; i<n2; i++) {
    tmp[i].data = null_index;
  }

  // copy current content into tmp
  mask = n2 - 1;
  r = pp->records;
  for (i=0; i<n; i++) {
    if (r->data != null_index) {
      ipart_copy_record(tmp, r, mask);
    }
    r ++;
  }

  // cleanup
  safe_free(pp->records);
  pp->records = tmp;
  pp->size = n2;
  pp->resize_threshold = (uint32_t) (n2 * IPART_RESIZE_RATIO);
}



/*
 * Allocate a new class: return it's id
 * - the new class vector is pp->classes[i]. It's initialized to NULL 
 */
static uint32_t allocate_class(ipart_t *pp) {
  uint32_t i, n;

  n = pp->csize;
  i = pp->nclasses;
  if (i == n) {
    // allocate or resize the classes array
    if (n == 0) {
      n = DEF_IPART_CSIZE;
      assert(n <= MAX_IPART_CSIZE);
    } else {
      n ++;
      n += n>>1; // 50% larger
      if (n > MAX_IPART_CSIZE) {
	out_of_memory();
      }
    }

    pp->classes = (int32_t **) safe_realloc(pp->classes, n * sizeof(int32_t *));
    pp->csize = n;
  }

  assert(i < pp->csize && pp->classes != NULL);
  pp->classes[i] = NULL;
  pp->nclasses = i+1;

  return i;
}


/*
 * Add x to the table:
 * - if there's y in the table that matches x
 *   then x is added to y's class. If y has no class attached
 *   yet, then a new class vector is allocated and both y and 
 *   x are added to that class.
 */
void int_partition_add(ipart_t *pp, int32_t x) {
  uint32_t mask, h, j;
  int32_t i;
  ipart_rec_t *r;

  assert(pp->nelems < pp->size);

  mask = pp->size - 1;
  h = pp->hash(pp->aux, x);  // hash code for x
  j = h & mask;
  for (;;) {
    r = pp->records + j;

    if (r->data == null_index) {
      // empty record found: ptr starts a new class
      r->hash = h;
      r->cid = -1; // no class attached yet
      r->data = x;
      pp->nelems ++;
      if (pp->nelems > pp->resize_threshold) {
	resize_int_partition(pp);
      }
      return;
    }

    if (r->hash == h && pp->match(pp->aux, x, r->data)) {
      // match found: add ptr to r's class
      i = r->cid;
      if (i < 0) {
	i = allocate_class(pp);
	r->cid = i;
	ipart_push(pp->classes + i, r->data);
      }
      ipart_push(pp->classes + i, x);
      return;
    }

    j ++;
    j &= mask;
  }
  
}
