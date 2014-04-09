/*
 * Queue + hset for breadth-first visit of a set of non-negative integers
 * (used for exploring terms)
 */

#ifndef __INT_HASH_QUEUE_H
#define __INT_HASH_QUEUE_H

#include <stdint.h>
#include <stdbool.h>

#include "int_hash_sets.h"
#include "int_queues.h"


/*
 * data structure = a queue + a hset
 */
typedef struct int_hqueue_s {
  int_queue_t queue;
  int_hset_t set;
} int_hqueue_t;


/*
 * Initialization: use default sizes for both hset and queue
 */
static inline void init_int_hqueue(int_hqueue_t *q) {
  init_int_queue(&q->queue, 0);
  init_int_hset(&q->set, 0);
}


/*
 * Deletion
 */
static inline void delete_int_hqueue(int_hqueue_t *q) {
  delete_int_queue(&q->queue);
  delete_int_hset(&q->set);
}


/*
 * Reset: empty the whole thing
 */
static inline void reset_int_hqueue(int_hqueue_t *q) {
  int_queue_reset(&q->queue);
  int_hset_reset(&q->set);
}


/*
 * Check whether x has been visited
 */
static inline bool int_hqueue_visited(int_hqueue_t *q, int32_t x) {
  assert(x >= 0);
  return int_hset_member(&q->set, x);
}

static inline bool int_hqueue_notvisited(int_hqueue_t *q, int32_t x) {
  return ! int_hqueue_visited(q, x);
}




/*
 * Check whether the queue is empty
 */
static inline bool int_hqueue_is_empty(int_hqueue_t *q) {
  return int_queue_is_empty(&q->queue);
}


/*
 * Get the first element in the queue and remove it
 * - q must be non-empty
 */
static inline int32_t int_hqueue_pop(int_hqueue_t *q) {
  return int_queue_pop(&q->queue);
}


/*
 * Add element x at the end of the queue and in the hset
 * - x must not be present in the set already
 */
static inline void int_hqueue_push(int_hqueue_t *q, int32_t x) {
  assert(! int_hqueue_visited(q, x));
  int_queue_push(&q->queue, x);
  (void) int_hset_add(&q->set, x);
}


#endif /* __INT_HASH_QUEUE_H */
