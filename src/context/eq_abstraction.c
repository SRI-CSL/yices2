/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Term partitions for equality abstract domain
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "context/eq_abstraction.h"


/*
 * Allocate a partition descriptor for n classes and m terms
 */
static epartition_t *alloc_epartition(uint32_t n, uint32_t m) {
  uint32_t size;
  epartition_t *tmp;

  size = n + m;
  if (size >= EPARTITION_MAX_SIZE) {
    out_of_memory();
  }
  tmp = (epartition_t *) safe_malloc(sizeof(epartition_t) + size * sizeof(term_t));
  tmp->nclasses = n;
  tmp->size = size;

  return tmp;
}



/*
 * Create a basic partition: two elements x and y in a single class
 * - x and y must be distinct
 */
epartition_t *basic_epartition(term_t x, term_t y) {
  epartition_t *tmp;

  assert(x != y);
  tmp = alloc_epartition(1, 2);
  tmp->data[0] = x;
  tmp->data[1] = y;
  tmp->data[2] = NULL_TERM;

  return tmp;
}



/*
 * Initialize manager m
 */
void init_epartition_manager(epartition_manager_t *m) {
  uint32_t i, n;

  n = EQABS_DEF_ESIZE;
  assert(n < EQABS_MAX_ESIZE);

  m->e_size = n;
  m->nterms = 0;
  m->label = (int32_t *) safe_malloc(n * sizeof(int32_t));
  m->next = (term_t *) safe_malloc(n * sizeof(term_t));

  // nothing stored: labels are all -1
  for (i=0; i<n; i++) {
    m->label[i] = -1;
  }

  n = EQABS_DEF_CSIZE;
  assert(n < EQABS_MAX_CSIZE);
  m->c_size = n;
  m->nclasses = 0;
  m->order = 0;
  m->root = (term_t *) safe_malloc(n * sizeof(term_t));

  n = EQABS_DEF_SCSIZE;
  assert(n < EQABS_MAX_SCSIZE);
  m->sc_size = n;
  m->subclass = (int32_t *) safe_malloc(n * sizeof(int32_t));

  // subclass[i] must be -1 for all i
  for (i=0; i<n; i++) {
    m->subclass[i] = -1;
  }

  init_ivector(&m->buffer, EQABS_BUFFER_SIZE);
  m->empty = alloc_epartition(0, 0);
}


/*
 * Delete all allocated memory
 */
void delete_epartition_manager(epartition_manager_t *m) {
  safe_free(m->label);
  safe_free(m->next);
  safe_free(m->root);
  safe_free(m->subclass);
  delete_ivector(&m->buffer);
  safe_free(m->empty);
  m->label = NULL;
  m->next = NULL;
  m->root = NULL;
  m->subclass = NULL;
  m->empty = NULL;
}


/*
 * Allocate a new class index. Make root array larger if necessary
 */
static int32_t get_class_index(epartition_manager_t *m) {
  int32_t i;
  uint32_t n;

  i = m->nclasses;
  n = m->c_size;
  if (i == n) {
    n += n >> 1; // make it 50% larger
    if (n >= EQABS_MAX_CSIZE) {
      out_of_memory();
    }
    m->root = (term_t *) safe_realloc(m->root, n * sizeof(term_t));
    m->c_size = n;
  }
  assert(i < m->c_size);
  m->nclasses = i+1;
  return i;
}


/*
 * Extend the label and next array: make them large enough to store term t
 * - no change if the arrays are large enough already
 */
static void resize_term_arrays(epartition_manager_t *m, term_t t) {
  uint32_t i, n;

  assert(t >= 0);

  n = m->e_size;
  if (t >= n) {
    // new_size = max(t+1, n+n/2)
    n += n>>1;
    if (t >= n) n = t+1;

    if (n >= EQABS_MAX_ESIZE) {
      out_of_memory();
    }
    m->label = (int32_t *) safe_realloc(m->label, n * sizeof(int32_t));
    m->next = (term_t *) safe_realloc(m->next, n * sizeof(term_t));

    for (i=m->e_size; i<n; i++) {
      m->label[i] = -1;
    }
    m->e_size = n;
  }
  assert(t < m->e_size);
}


/*
 * Make sure the subclass array is large enough for n subclasses
 */
static void resize_subclass_array(epartition_manager_t *m, uint32_t n) {
  uint32_t i, k;

  k = m->sc_size;
  if (k < n) {
    // new_size = max(n, k+k/2)
    k += k>>1;
    if (k < n) k = n;

    if (k >= EQABS_MAX_SCSIZE) {
      out_of_memory();
    }
    m->subclass = (int32_t *) safe_realloc(m->subclass, k * sizeof(int32_t));

    // initialize all subclasses to -1
    for (i=m->sc_size; i<k; i++) {
      m->subclass[i] = -1;
    }
    m->sc_size = k;
  }
  assert(n <= m->sc_size);
}





/*
 * CONSTRUCTION OF PARTITION OBJECTS
 */


/*
 * Convert the partition stored in m into an epartition object
 * If a class c is marked (m->root[c] < 0) then it's skipped
 * Side-effect: reset m, but does not reset the labels.
 */
static epartition_t *get_epartition(epartition_manager_t *m) {
  uint32_t i, j, n;
  term_t t, r;
  epartition_t *tmp;

  if (m->order == 0) {
    // empty partition
    assert(m->nterms == 0);
    tmp = m->empty;
  } else {
    // build a partition object
    tmp = alloc_epartition(m->order, m->nterms);
    n = m->nclasses;
    j = 0;
    for (i=0; i<n; i++) {
      r = m->root[i];
      if (r >= 0) {
        t = r;
        do {
          assert(j < tmp->size);
          tmp->data[j] = t;
          j ++;
          t = m->next[t];
        } while (t != r);
        assert(j < tmp->size);
        tmp->data[j] = NULL_TERM; // end marker
        j ++;
      }
    }
    assert(j == tmp->size);
  }

  m->nclasses = 0;
  m->order = 0;
  m->nterms = 0;

  return tmp;
}


/*
 * Clear the labels of all terms in p
 */
static void epartition_clear_labels(epartition_manager_t *m, epartition_t *p) {
  uint32_t i, n;
  term_t *q, t;

  q = p->data;
  n = p->size;
  for (i=0; i<n; i++) {
    t = q[i];
    if (t >= 0) {
      assert(t < m->e_size);
      m->label[t] = -1;
    }
  }
}





/*
 * MERGE OPERATIONS
 */

/*
 * Meet/merge operations construct a partition in m by merging classes
 * In this mode, the label array stores the class of terms in the partition
 * being constructed.
 */


#ifndef NDEBUG

/*
 * For debugging: check whether i is a good class index
 */
static bool epartition_good_class(epartition_manager_t *m, int32_t i) {
  term_t r;

  if (i<0 || i>= m->nclasses) return false;
  r = m->root[i];
  return 0 <= r && r < m->e_size && m->label[r] == i;
}

#endif


/*
 * Read the class id for term t
 * -1 means t is not in any class
 */
static int32_t epartition_class_of_term(epartition_manager_t *m, term_t t) {
  assert(t >= 0);
  return (t < m->e_size) ? m->label[t] : -1;
}

/*
 * Allocate a new class with unique element t
 * - t must not be in any other class
 * - return the new class index
 */
static int32_t epartition_start_class(epartition_manager_t *m, term_t t) {
  int32_t i;

  resize_term_arrays(m, t);
  assert(m->label[t] == -1);
  i = get_class_index(m);
  m->root[i] = t;
  m->label[t] = i;
  m->next[t] = t;
  m->nterms ++;
  m->order ++;

  return i;
}


/*
 * Add term t to an existing class i
 * - t must not be in any class yet and t must be >= 0
 */
static void epartition_add_to_class(epartition_manager_t *m, term_t t, int32_t i) {
  term_t r;

  assert(epartition_good_class(m, i));

  resize_term_arrays(m, t);
  assert(m->label[t] == -1);

  m->label[t] = i;
  r = m->root[i];
  m->next[t] = m->next[r];
  m->next[r] = t;
  m->nterms ++;
}


/*
 * Merge classes i and j (into class i)
 * - relabel all elements in class j
 * - merge the lists
 * - mark that class j does not exist anymore
 *
 * NOTE: this could be inefficient if class j is large
 * (could use a union-find structure for this)
 */
static void epartition_merge_classes(epartition_manager_t *m, int32_t i, int32_t j) {
  term_t t, r, s;

  assert(i != j && epartition_good_class(m, i) && epartition_good_class(m, j));

  // fix the labels
  r = m->root[j];
  t = r;
  do {
    m->label[t] = i;
    t = m->next[t];
  } while (t != r);

  // merge the lists by swapping next[root[i]] and next[root[j]]
  s = m->root[i];
  t = m->next[r];
  m->next[r] = m->next[s];
  m->next[s] = t;

  // mark class j
  m->root[j] = NULL_TERM;
  m->order --;
}


/*
 * Copy partition p into m, in preparation for a meet operation
 */
void epartition_init_for_meet(epartition_manager_t *m, epartition_t *p) {
  term_t *q, t;
  uint32_t i, n;
  int32_t c;

  assert(m->nclasses == 0 && m->nterms == 0 && m->order == 0);
  q = p->data;
  n = p->nclasses;
  for (i=0; i<n; i++) {
    t = *q ++;
    c = epartition_start_class(m, t);
    // each class in p should have at least two elements
    t = *q ++;
    do {
      epartition_add_to_class(m, t, c);
      t = *q ++;
    } while (t >= 0);
  }
}


/*
 * Compute the meet of partition in m and p:
 * - for any terms t u in a class of p,
 *   merge the class of t and the class of u in m
 */
void epartition_meet(epartition_manager_t *m, epartition_t *p) {
  term_t *q, t;
  uint32_t i, n;
  int32_t c, d;

  q = p->data;
  n = p->nclasses;
  for (i=0; i<n; i++) {
    t = *q ++;
    // first term: create a new class if t is not in m
    c = epartition_class_of_term(m, t);
    if (c < 0) {
      c = epartition_start_class(m, t);
    }

    // for every other term t: either merge the class of t and c or add t to c
    t = *q ++;
    do {
      d = epartition_class_of_term(m, t);
      if (d < 0) {
        epartition_add_to_class(m, t, c);
      } else if (d != c) {
        epartition_merge_classes(m, d, c);
        c = d;
      }
      t = *q ++;
    } while (t >= 0);
  }
}



/*
 * Convert the current partition (in a meet operation)
 * to a partition object
 */
epartition_t *epartition_get_meet(epartition_manager_t *m) {
  epartition_t *tmp;

  tmp = get_epartition(m);
  epartition_clear_labels(m, tmp);

  return tmp;
}


/*
 * SPLIT OPERATIONS
 */

/*
 * Split/join operations construct a partition in m by splitting classes of m
 * into smaller subclasses. In this mode, terms are not labeled by their
 * class id, but the label array is used internally by epartition_join
 */

/*
 * Start a new class with unique element t
 * - t must not be in any class yet
 * - return the new class index
 * - update order and nterms
 */
static int32_t epartition_start_join_class(epartition_manager_t *m, term_t t) {
  int32_t i;

  resize_term_arrays(m,t);
  i = get_class_index(m);
  m->root[i] = t;
  m->next[t] = t;
  m->nterms ++;
  m->order ++;

  return i;
}

/*
 * Add t to an existing class i
 * - t must not be in any class yet
 * - update nterms
 */
static void epartition_add_to_join_class(epartition_manager_t *m, term_t t, int32_t i) {
  term_t r;

  resize_term_arrays(m, t);
  r = m->root[i];
  m->next[t] = m->next[r];
  m->next[r] = t;
  m->nterms ++;
}


/*
 * For each term in class i of p, set label[t] to i in m
 */
static void epartition_set_labels(epartition_manager_t *m, epartition_t *p) {
  uint32_t i, n;
  term_t *q, t;

  q = p->data;
  n = p->nclasses;
  for (i=0; i<n; i++) {
    t = * q++;
    resize_term_arrays(m, t);
    m->label[t] = i;
    t = * q++;
    do {
      resize_term_arrays(m, t);
      m->label[t] = i;
      t = *q ++;
    } while (t >= 0);
  }
}


/*
 * Add element t to subclass[i]
 * - create a new subclass if needed
 */
static void epartition_add_to_subclass(epartition_manager_t *m, term_t t, int32_t i) {
  int32_t c;
  term_t r;

  c = m->subclass[i];
  if (c < 0) {
    c = get_class_index(m);
    m->subclass[i] = c;
    m->order ++;
    m->root[c] = t;
    m->next[t] = t;
  } else {
    r = m->root[c];
    m->next[t] = m->next[r];
    m->next[r] = t;
  }
}


/*
 * Follow list of terms starting with r
 * - move every term into a separate subclass, based on their label
 * - subclass[i] = all terms t in the list such that label[t] == i
 * - terms such that label[t] = -1 are removed
 * Requirement:
 * - subclass array must be large enough
 * - for each i subclass[i] must be -1
 */
static void refine_class(epartition_manager_t *m, term_t r) {
  uint32_t i, n;
  term_t t, nxt;
  int32_t j;

  n = m->nclasses;
  t = r;
  do {
    j = m->label[t];
    nxt = m->next[t];
    if (j < 0) {
      m->nterms --;
    } else {
      epartition_add_to_subclass(m, t, j);
    }
    t = nxt;
  } while (t != r);

  // clear the subclasses
  for (i=n; i<m->nclasses; i++) {
    t = m->root[i];
    j = m->label[t];
    assert(j >= 0 && m->subclass[j] == i);
    m->subclass[j] = -1;
  }
}


/*
 * Remove the singleton classes from m
 * - each class that gets removed is marked by setting root[i] to NULL_TERM
 */
static void epartition_remove_singletons(epartition_manager_t *m) {
  uint32_t i, n;
  term_t r;

  n = m->nclasses;
  for (i=0; i<n; i++) {
    r = m->root[i];
    if (r >= 0 && m->next[r] == r) {
      assert(m->nterms > 0 && m->order > 0);
      m->root[i] = NULL_TERM;
      m->label[r] = -1;
      m->nterms --;
      m->order --;
    }
  }
}



/*
 * Copy partition p into m, in preparation for join
 */
void epartition_init_for_join(epartition_manager_t *m, epartition_t *p) {
  term_t *q, t;
  uint32_t i, n;
  int32_t c;

  assert(m->nclasses == 0 && m->nterms == 0 && m->order == 0);
  q = p->data;
  n = p->nclasses;
  for (i=0; i<n; i++) {
    t = *q ++;
    c = epartition_start_join_class(m, t);
    t = *q ++;
    do {
      epartition_add_to_join_class(m, t, c);
      t = *q ++;
    } while (t >= 0);
  }
}


/*
 * Refine the partition stored in m:
 * - (t == u) are in the same class in the result
 *   iff they are in the same class in m and in p
 */
void epartition_join(epartition_manager_t *m, epartition_t *p) {
  uint32_t i, n;
  ivector_t *v;
  term_t t;

  resize_subclass_array(m, p->nclasses);
  epartition_set_labels(m, p);

  // copy all classes in the internal buffer
  v = &m->buffer;
  assert(v->size == 0);
  n = m->nclasses;
  for (i=0; i<n; i++) {
    t = m->root[i];
    if (t >= 0) {
      ivector_push(v, t);
    }
  }
  m->nclasses = 0;
  m->order = 0;

  // refine all classes in the buffer
  n = v->size;
  for (i=0; i<n; i++) {
    refine_class(m, v->data[i]);
  }

  // cleanup: remove singleton classes and clear labels
  ivector_reset(v);
  epartition_remove_singletons(m);
  epartition_clear_labels(m, p);
}


/*
 * Construct the partition p stored in m
 */
epartition_t *epartition_get_join(epartition_manager_t *m) {
  return get_epartition(m);
}
