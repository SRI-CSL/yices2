/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Hash table that maps extended rationals to non-negative integers
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/hash_functions.h"
#include "terms/rational_hash_maps.h"


/*
 * For debugging: check whether n is a power of 2 (or 0)
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialization
 * - n = initial size of the table
 * - if n = 0, the default size is used. Otherwise n must be
 *   a power of 2
 */
void init_xq_hmap(xq_hmap_t *hmap, uint32_t n) {
  uint32_t i;
  xq_hmap_rec_t *tmp;

  if (n == 0) {
    n = XQ_HMAP_DEFAULT_SIZE;
  }

  if (n >= XQ_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (xq_hmap_rec_t *) safe_malloc(n * sizeof(xq_hmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].value = 0;
    xq_init(&tmp[i].key);
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->nentries = 0;
  hmap->ndeleted = 0;
  hmap->resize_threshold = (uint32_t)(n * XQ_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n * XQ_HMAP_CLEANUP_RATIO);
}



/*
 * Delete: free all rationals and delete the table
 */
void delete_xq_hmap(xq_hmap_t *hmap) {
  xq_hmap_rec_t *tmp;
  uint32_t i, n;

  tmp = hmap->data;
  n = hmap->size;
  for (i=0; i<n; i++) {
    xq_clear(&tmp[i].key);
  }

  safe_free(tmp);
  hmap->data = NULL;
}



/*
 * Reset: empty the table
 */
void reset_xq_hmap(xq_hmap_t *hmap) {
  xq_hmap_rec_t *tmp;
  uint32_t i, n;

  tmp = hmap->data;
  n = hmap->size;
  for (i=0; i<n; i++) {
    tmp[i].value = 0;
    xq_clear(&tmp[i].key);
  }

  hmap->nelems = 0;
  hmap->nentries = 0;
  hmap->ndeleted = 0;
}



/*
 * Hash code for extended rational q
 */
static uint32_t hash_xq(xrational_t *q) {
  uint32_t a, b, c, d;

  q_hash_decompose(&q->main, &a, &b);
  q_hash_decompose(&q->delta, &c, &d);

  return jenkins_hash_quad(a, b, c, d, 0xd12ae3f7);
}



/*
 * Fresh copy:
 * - copy the content of record r into a fresh table a
 * - mask = size of a - 1 (where size of a is a power of 2)
 * - there must be room for the new record in array a
 * - r must be a non-null record (i.e., r->value > 0)
 * - WARNING: this makes a shallow copy of r->key,
 *   so don't call xq_clear(&r->key)
 */
static void xq_hmap_clean_copy(xq_hmap_rec_t *a, xq_hmap_rec_t *r, uint32_t mask) {
  uint32_t j;

  assert(r->value> 0);

  j = hash_xq(&r->key) & mask;
  while (a[j].value > 0) {
    j ++;
    j &= mask;
  }

  a[j].value = r->value;
  a[j].key = r->key;
}



/*
 * Remove all the deleted records
 */
static void xq_hmap_cleanup(xq_hmap_t *hmap) {
  xq_hmap_rec_t *tmp, *r;
  uint32_t i, n, mask;

  n = hmap->size;
  assert(is_power_of_two(n));

  tmp = (xq_hmap_rec_t *) safe_malloc(n * sizeof(xq_hmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].value = 0;
    xq_init(&tmp[i].key);
  }

  mask = n - 1;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (r->value > 0 && r->value != UINT32_MAX) {
      xq_hmap_clean_copy(tmp, r, mask);
    }
    r ++;
  }

  /*
   * We don't clear the rationals from hmap->data here
   * since they've been copied into the new array tmp.
   */
  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n;
  hmap->ndeleted = 0;
}



/*
 * Make the table twice as large.
 * Remove the deleted records.
 */
static void xq_hmap_extend(xq_hmap_t *hmap) {
  xq_hmap_rec_t *tmp, *r;
  uint32_t i, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= XQ_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n2));

  tmp = (xq_hmap_rec_t *) safe_malloc(n2 * sizeof(xq_hmap_rec_t));
  for (i=0; i<n2; i++) {
    tmp[i].value = 0;
    xq_init(&tmp[i].key);
  }

  mask = n2 - 1;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (r->value > 0 && r->value != UINT32_MAX) {
      // live record
      xq_hmap_clean_copy(tmp, r, mask);
    }
    r ++;
  }

  /*
   * We don't clear the rationals from hmap->data here
   * since they've been copied into the new array tmp.
   */
  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n2 * XQ_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n2 * XQ_HMAP_CLEANUP_RATIO);
}



/*
 * Find the value attached to key q
 * - return 0 if there's no record with key q
 */
uint32_t xq_hmap_multiplicity(xq_hmap_t *hmap, xrational_t *q) {
  xq_hmap_rec_t *r;
  uint32_t i, mask, v;

  assert(hmap->nelems < hmap->size); // otherwise the function may loop

  mask = hmap->size - 1;
  i = hash_xq(q) & mask;
  for (;;) {
    r = hmap->data + i;
    v = r->value;
    if (v == 0 || (v != UINT32_MAX && xq_eq(&r->key, q))) {
      return v;
    }
    i ++;
    i &= mask;
  }
}





/*
 * Add an entry of key = q
 * - if there's a record r with r->key = q already, increment r->value
 * - otherwise create a new record with r->key = q, r->value = 1
 */
void xq_hmap_add_entry(xq_hmap_t *hmap, xrational_t *q) {
  xq_hmap_rec_t *r, *s;
  uint32_t i, mask;

  assert(hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i = hash_xq(q) & mask;
  for (;;) {
    r = hmap->data + i;
    if (r->value == 0) goto add;
    if (r->value == UINT32_MAX) break;
    if (xq_eq(&r->key, q)) {
      r->value ++;
      goto done;
    }
    i ++;
    i &= mask;
  }

  // r is marked as deleted
  // the new record if needed will be stored in *r
  for (;;) {
    i ++;
    i &= mask;
    s = hmap->data + i;
    if (s->value == 0) goto add;
    if (s->value != UINT32_MAX && xq_eq(&s->key, q)) {
      s->value ++;
      goto done;
    }
  }

 add:
  // add a new record in r
  r->value = 1;
  xq_set(&r->key, q);
  hmap->nelems ++;
  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    xq_hmap_extend(hmap);
  }

 done:
  hmap->nentries ++;
}



/*
 * Remove an entry of key q
 * - there must be a record with that key in the table.
 */
void xq_hmap_remove_entry(xq_hmap_t *hmap, xrational_t *q) {
  xq_hmap_rec_t *r;
  uint32_t i, mask;

  assert(xq_hmap_has_entry(hmap, q));

  mask = hmap->size - 1;
  i = hash_xq(q) & mask;
  for (;;) {
    r = hmap->data + i;
    if (r->value != UINT32_MAX && xq_eq(&r->key, q)) break;
    i ++;
    i &= mask;
  }

  assert(xq_eq(&r->key, q) && r->value > 0 && r->value != UINT32_MAX && hmap->nentries > 0);
  hmap->nentries --;
  r->value --;
  if (r->value == 0) {
    r->value = UINT32_MAX;
    xq_clear(&r->key);
    hmap->nelems --;
    hmap->ndeleted ++;
    if (hmap->ndeleted >= hmap->cleanup_threshold) {
      xq_hmap_cleanup(hmap);
    }
  }
}




/*
 * Copy the content of r into a fresh table a.
 * This is like clean_copy above except that it makes a real
 * copy of r->key (rather than a shallow copy).
 * - mask = size of a - 1 (the size of a must be a power of 2)
 */
static void xq_hmap_clean_copy2(xq_hmap_rec_t *a, xq_hmap_rec_t *r, uint32_t mask) {
  uint32_t j;

  assert(r->value> 0);

  j = hash_xq(&r->key) & mask;
  while (a[j].value > 0) {
    j ++;
    j &= mask;
  }

  a[j].value = r->value;
  xq_set(&a[j].key, &r->key);
}


/*
 * Copy the content of hmap2 into hmap1
 * - hmap1 must be initialized
 * - if hmap1 is not empty, it's reset first
 */
void copy_xq_hmap(xq_hmap_t *hmap1, xq_hmap_t *hmap2) {
  xq_hmap_rec_t *tmp, *r;
  uint32_t i, n1, n2, mask;

  if (hmap1->nelems + hmap1->ndeleted > 0) {
    reset_xq_hmap(hmap1);
  }

  assert(hmap1->nentries == 0 && hmap1->nelems == 0 &&
         hmap1->ndeleted == 0);


  n1 = hmap1->size;
  mask = n1 - 1;
  tmp = hmap1->data;

  n2 = hmap2->size;

  assert(is_power_of_two(n1) && is_power_of_two(n2));

  if (n1 < n2) {
    // make sure hmap1 is at least as large as hmap2
    assert(n2 < XQ_HMAP_MAX_SIZE);
    safe_free(tmp);

    tmp = (xq_hmap_rec_t *) safe_malloc(n2 * sizeof(xq_hmap_rec_t));
    for (i=0; i<n2; i++) {
      tmp[i].value = 0;
      xq_init(&tmp[i].key);
    }

    mask = n2 - 1;
    hmap1->data = tmp;
    hmap1->size = n2;
    hmap1->resize_threshold = (uint32_t) (n2 * XQ_HMAP_RESIZE_RATIO);
    hmap2->cleanup_threshold = (uint32_t) (n2 * XQ_HMAP_CLEANUP_RATIO);
  }

  r = hmap2->data;
  for (i=0; i<n2; i++) {
    if (r->value > 0 && r->value != UINT32_MAX) {
      xq_hmap_clean_copy2(tmp, r, mask);
    }
    r ++;
  }

  hmap1->nentries = hmap2->nentries;
  hmap1->nelems = hmap2->nelems;
}



/*
 * Shift entry q by delta
 * - q must be present in the table.
 * - this removes one entry for q and add one entry for (q + delta)
 */
void xq_hmap_shift_entry(xq_hmap_t *hmap, xrational_t *q, rational_t *delta) {
  xrational_t aux;

  xq_init(&aux);
  xq_set(&aux, q);
  xq_add_q(&aux, delta);

  xq_hmap_remove_entry(hmap, q);
  xq_hmap_add_entry(hmap, &aux);
  xq_clear(&aux);
}


/*
 * Variant: shift entry q by a * delta
 */
void xq_hmap_addmul_entry(xq_hmap_t *hmap, xrational_t *q, rational_t *a, rational_t *delta) {
  xrational_t aux;

  xq_init(&aux);
  xq_set(&aux, q);
  q_addmul(&aux.main, a, delta);

  xq_hmap_remove_entry(hmap, q);
  xq_hmap_add_entry(hmap, &aux);
  xq_clear(&aux);
}


/*
 * Variant: shift entry q by - a * delta
 */
void xq_hmap_submul_entry(xq_hmap_t *hmap, xrational_t *q, rational_t *a, rational_t *delta) {
  xrational_t aux;

  xq_init(&aux);
  xq_set(&aux, q);
  q_submul(&aux.main, a, delta);

  xq_hmap_remove_entry(hmap, q);
  xq_hmap_add_entry(hmap, &aux);
  xq_clear(&aux);
}


