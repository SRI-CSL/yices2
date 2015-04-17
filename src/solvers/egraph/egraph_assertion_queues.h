/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Queue for storing assertions sent by egraph to theory solvers.
 * Solvers must process these assertions when propagate is called.
 *
 * The assertions are of the following forms:
 *   v1 == v2 with an id
 *   v1 != v2 with a hint
 *   distinct v[0] ... v[n-1] with a hint
 * where v1, v2, etc. are theory variable. The hint is a composite_t
 * object that the egraph requires to generate explanations.
 * For (v1 == v2), the id is the index of an egraph edge, that's also
 * used to generate explanations.
 *
 * Each assertion is stored as the following data
 * - tag: encode the assertion type (eq, diseq, distinct)
 *        and number of variables (2 or n)
 * - hint: is stored as is for explanation
 * - v[0 ... n-1]: the variables involved
 */

#ifndef __EGRAPH_ASSERTION_QUEUES_H
#define __EGRAPH_ASSERTION_QUEUES_H

#include <stdint.h>
#include <stddef.h>
#include <limits.h>
#include <assert.h>

#include "solvers/egraph/egraph_types.h"


/*
 * Assertion types
 */
typedef enum eassertion_kind {
  EGRAPH_VAR_EQ,
  EGRAPH_VAR_DISEQ,
  EGRAPH_VAR_DISTINCT,
} eassertion_kind_t;

/*
 * Assertion descriptor
 * - the tag encodes kind + arity
 */
typedef struct eassertion_s {
  composite_t *hint;
  uint32_t tag;
  int32_t id;
  thvar_t var[0]; // real size depends on arity
} eassertion_t;


/*
 * Tag constructor
 * - 2 low order bits encode the kind
 * - 30 high order bits contain the arity
 */
#define MAX_EASSERTION_ARITY (1<<30)
#define EASSERTION_KIND_MASK ((uint32_t) 0x3)

static inline uint32_t mk_eassertion_tag(eassertion_kind_t k, uint32_t n) {
  assert (n < MAX_EASSERTION_ARITY);
  return (n << 2) | k;
}

static inline uint32_t mk_var_eq_tag(void) {
  return mk_eassertion_tag(EGRAPH_VAR_EQ, 2);
}

static inline uint32_t mk_var_diseq_tag(void) {
  return mk_eassertion_tag(EGRAPH_VAR_DISEQ, 2);
}

static inline uint32_t mk_var_distinct_tag(uint32_t n) {
  return mk_eassertion_tag(EGRAPH_VAR_DISTINCT, n);
}


/*
 * Extract kind and arity from the tag
 */
static inline eassertion_kind_t eassertion_tag_kind(uint32_t tag) {
  return (eassertion_kind_t) (tag & EASSERTION_KIND_MASK);
}

static inline uint32_t eassertion_tag_arity(uint32_t tag) {
  return tag>>2;
}


/*
 * Size of an assertion object of arity n:
 * - on 64bit machines, we round the size up to a multiple of 8
 */
static inline size_t align_size(size_t d) {
#if (ULONG_MAX == 4294967295UL)
  return (d + 3) & ~((size_t) 3); // 32 bits
#elif (ULONG_MAX == 18446744073709551615UL)
  return (d + 7) & ~((size_t) 7);  // 64 bits
#else
#error Could not find pointer alignment
#endif
}

static inline uint32_t sizeof_eassertion(uint32_t n) {
  return (uint32_t) align_size(sizeof(eassertion_t) + n * sizeof(uint32_t));
}



/*
 * Extract the kind, arity, size from an assertion a
 */
static inline eassertion_kind_t eassertion_get_kind(eassertion_t *a) {
  return eassertion_tag_kind(a->tag);
}

static inline uint32_t eassertion_get_arity(eassertion_t *a) {
  return eassertion_tag_arity(a->tag);
}

static inline size_t eassertion_get_size(eassertion_t *a) {
  return sizeof_eassertion(eassertion_get_arity(a));
}





/*
 * Assertion queue: resizable byte array where
 * the descriptors are copied
 * - data[0 ... top-1] = where existing assertions are copied
 * the full array has size bytes
 */
typedef struct eassertion_queue_s {
  uint32_t size;  // full size
  uint32_t top;   // allocation pointer
  uint8_t *data;  // storage
} eassertion_queue_t;

#define DEF_EASSERTION_QUEUE_SIZE 10000
#define MAX_EASSERTION_QUEUE_SIZE UINT32_MAX


/*
 * Initialize the queue (empty)
 */
extern void init_eassertion_queue(eassertion_queue_t *queue);

/*
 * Delete the queue: free all memory
 */
extern void delete_eassertion_queue(eassertion_queue_t *queue);


/*
 * Empty the queue
 */
static inline void reset_eassertion_queue(eassertion_queue_t *queue) {
  queue->top = 0;
}


/*
 * Add assertions to the queue
 */
extern void eassertion_push_eq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, int32_t id);
extern void eassertion_push_diseq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, composite_t *hint);
extern void eassertion_push_distinct(eassertion_queue_t *queue, uint32_t n, thvar_t *a, composite_t *hint);



/*
 * Operation to scan the queue: nothing can be added to the queue
 * while these operations are being used.
 */

/*
 * Check whether the queue is empty
 */
static inline bool eassertion_queue_is_empty(eassertion_queue_t *queue) {
  return queue->top == 0;
}

static inline bool eassertion_queue_is_nonempty(eassertion_queue_t *queue) {
  return queue->top > 0;
}

/*
 * First assertion in the queue
 */
static inline eassertion_t *eassertion_queue_start(eassertion_queue_t *queue) {
  return (eassertion_t *) queue->data;
}

/*
 * Get the end pointer
 */
static inline eassertion_t *eassertion_queue_end(eassertion_queue_t *queue) {
  return (eassertion_t *) (queue->data + queue->top);
}

/*
 * Pointer to the assertion that follows a in queue->data
 */
static inline eassertion_t *eassertion_next(eassertion_t *a) {
  return (eassertion_t *) (((uint8_t *) a) + eassertion_get_size(a));
}




#endif /* __EGRAPH_ASSERTION_QUEUES_H */
