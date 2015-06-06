/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * COMMON CONJUNCTS IN A SET OF FORMULAS
 *
 * Given n formulas f[0] ... f[n-1], where each f[i] is seen as
 * conjunction of formuals. This module computes the sub-formulas that
 * are common to all f[i].
 *
 * This is useful to rewrite assertions like
 *   (OR (AND A B_1) (AND A B_2) ... (AND A B_n))
 * to
 *   (AND A (OR B_1 B_2 ... B_n))
 */

#include <assert.h>

#include "context/common_conjuncts.h"
#include "utils/int_array_sort.h"


/*
 * Initialization: use default sizes for queue, hset, and vectors
 */
void init_bfs_explorer(bfs_explorer_t *explorer, term_table_t *terms) {
  explorer->terms = terms;
  init_int_queue(&explorer->queue, 0);
  init_int_hset(&explorer->hset, 0);
  init_ivector(&explorer->aux1, 10);
  init_ivector(&explorer->aux2, 10);
}


/*
 * Reset: empty queue and hset
 */
void reset_bfs_explorer(bfs_explorer_t *explorer) {
  int_queue_reset(&explorer->queue);
  int_hset_reset(&explorer->hset);
  ivector_reset(&explorer->aux1);
  ivector_reset(&explorer->aux2);
}


/*
 * Delete: free memory
 */
void delete_bfs_explorer(bfs_explorer_t *explorer) {
  delete_int_queue(&explorer->queue);
  delete_int_hset(&explorer->hset);
  delete_ivector(&explorer->aux1);
  delete_ivector(&explorer->aux2);
}


/*
 * BFS traversal: the hset contains the set of terms visited so far
 * - bfs_explorer_push_term: add t to the queue if t has not been visited yet
 * - also add t to hest
 */
static void bfs_explorer_push_term(bfs_explorer_t *explorer, term_t t) {
  if (int_hset_add(&explorer->hset, t)) {
    int_queue_push(&explorer->queue, t);
  }
}


/*
 * CONJUNCTS
 */

/*
 * Process all terms in the queue and extract conjuncts
 */
static void bfs_collect_conjuncts(bfs_explorer_t *explorer, ivector_t *v) {
  term_table_t *terms;
  composite_term_t *or;
  uint32_t i, n;
  term_t t;

  terms = explorer->terms;

  while (! int_queue_is_empty(&explorer->queue)) {
    t = int_queue_pop(&explorer->queue);
    assert(is_boolean_term(terms, t));

    if (is_neg_term(t) && term_kind(terms, t) == OR_TERM) {
      /*
       * t is (not (or a[0] ... a[n-1])), 
       * we push (not a[0]) ... (not a[n-1]) into the queue.
       */
      or = or_term_desc(terms, t);
      n = or->arity;
      for (i=0; i<n; i++) {
	bfs_explorer_push_term(explorer, opposite_term(or->arg[i]));
      }
    } else {
      /*
       * t is a conjunct
       */
      ivector_push(v, t);
    }
  }

  // empty the hset
  int_hset_reset(&explorer->hset);
}


/*
 * Compute the conjuncts of formula f
 * - the conjuncts are stored in vector v
 * - v is reset first
 */ 
void bfs_get_conjuncts(bfs_explorer_t *explorer, term_t f, ivector_t *v) {
  assert(int_queue_is_empty(&explorer->queue));
  assert(int_hset_is_empty(&explorer->hset));

  ivector_reset(v);
  bfs_explorer_push_term(explorer, f);
  bfs_collect_conjuncts(explorer, v);
}



/*
 * DISJUNCTS
 */

/*
 * Process all terms in the queue and extract conjuncts
 */
static void bfs_collect_disjuncts(bfs_explorer_t *explorer, ivector_t *v) {
  term_table_t *terms;
  composite_term_t *or;
  uint32_t i, n;
  term_t t;

  terms = explorer->terms;

  while (! int_queue_is_empty(&explorer->queue)) {
    t = int_queue_pop(&explorer->queue);
    assert(is_boolean_term(terms, t));

    if (is_pos_term(t) && term_kind(terms, t) == OR_TERM) {
      /*
       * t is (or a[0] ... a[n-1])), 
       * we push a[0] ... a[n-1] into the queue.
       */
      or = or_term_desc(terms, t);
      n = or->arity;
      for (i=0; i<n; i++) {
	bfs_explorer_push_term(explorer, or->arg[i]);
      }
    } else {
      /*
       * t is a disjunct
       */
      ivector_push(v, t);
    }
  }

  // empty the hset
  int_hset_reset(&explorer->hset);
}




/*
 * Compute the disjuncts of formula f
 * - store them in vector v
 */
void bfs_get_disjuncts(bfs_explorer_t *explorer, term_t f, ivector_t *v) {
  assert(int_queue_is_empty(&explorer->queue));
  assert(int_hset_is_empty(&explorer->hset));

  ivector_reset(v);
  bfs_explorer_push_term(explorer, f);
  bfs_collect_disjuncts(explorer, v);
}



/*
 * COMMON CONJUNCTS
 */

/*
 * Store the intersection of v1 and v2 in v1
 * - the two vectors must be sorted in increasing order
 */
static void intersect_vectors(ivector_t *v1, ivector_t *v2) {
  uint32_t i, j, k, n1, n2;
  term_t t;

  n1 = v1->size;
  n2 = v2->size;

  j = 0;
  k = 0;
  for (i=0; i<n1; i++) {
    t = v1->data[i];
    while (k < n2 && t > v2->data[k]) {
      k ++;
    }
    if (k == n2) break;
    if (t == v2->data[k]) {
      v1->data[j] = t;
      j ++;
      k ++;
    }
  }

  ivector_shrink(v1, j);
}

/*
 * Compute the common conjuncts of formulas f[0 ... n-1]
 * - n must be positive
 * - store them in vector v (sorted)
 * - v is reset first
 */
void bfs_get_common_conjuncts(bfs_explorer_t *explorer, term_t *f, uint32_t n, ivector_t *v) {
  ivector_t *aux1;
  uint32_t i;

  assert(n > 0);

  aux1 = &explorer->aux1;
  assert(aux1->size == 0);

  bfs_get_conjuncts(explorer, f[0], v);
  int_array_sort(v->data, v->size);
  for (i=1; i<n; i++) {    
    bfs_get_conjuncts(explorer, f[i], aux1);
    int_array_sort(aux1->data, aux1->size);
    intersect_vectors(v, aux1);
    ivector_reset(aux1);
    if (v->size == 0) break;
  }
}



/*
 * COMMON FACTORS
 */

/*
 * If f is of the form (or a[0] ... a[n-1]), this function collects all
 * the subformulas that are common conjuncts of a[0] ... a[n-1].
 * So we have a[i] = (and (common-factors b[i]))
 *    and f is equivalent to (and common-factors (or b[0] ... b[n-1])))
 *
 * If f is not of the form (or ...), then the unique common factor is f itself.
 * This function stores f in v in this case.
 */
void bfs_factor_disjunction(bfs_explorer_t *explorer, term_t f, ivector_t *v) {
  ivector_t *aux2;

  aux2 = &explorer->aux2;
  assert(aux2->size == 0);

  bfs_get_disjuncts(explorer, f, aux2);
  if (aux2->size == 1) {
    ivector_push(v, aux2->data[0]);
  } else {
    bfs_get_common_conjuncts(explorer, aux2->data, aux2->size, v);
  }

  ivector_reset(aux2);  
}
