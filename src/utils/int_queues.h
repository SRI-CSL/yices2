/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * QUEUES OF 32BIT SIGNED INTEGERS
 */

#ifndef __INT_QUEUES_H
#define __INT_QUEUES_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Components:
 * - data = integer array to store the elements
 * - size = size of that array
 * - head, tail = indices between 0 and size - 1.
 * The queue is managed as a circular array:
 * - if head = tail, the queue is empty
 * - if head < tail, the queue content is data[head ... tail-1]
 * - if head > tail, the queue content is
 *     data[head...size-1] + data[0 ... tail-1]
 */
typedef struct int_queue_s {
  int32_t *data;
  uint32_t size;
  uint32_t head;
  uint32_t tail;
} int_queue_t;


/*
 * Maximal size: make sure n * sizeof(int32_t) does not overflow
 */
#define MAX_INT_QUEUE_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Default size
 */
#define DEFAULT_INT_QUEUE_INITIAL_SIZE 16


/*
 * Initialize a queue of size n.
 * If n = 0 then DEFAULT_QUEUE_INITIAL_SIZE is used.
 */
extern void init_int_queue(int_queue_t *q, uint32_t n);


/*
 * Delete q
 */
extern void delete_int_queue(int_queue_t *q);


/*
 * Push element x in the queue (at the end)
 */
extern void int_queue_push(int_queue_t *q, int32_t x);


/*
 * Push a[0 ... n-1] in the queue (in this order)
 */
extern void int_queue_push_array(int_queue_t *q, int32_t *a, uint32_t n);


/*
 * Check whether the queue is empty
 */
static inline bool int_queue_is_empty(int_queue_t *q) {
  return q->head == q->tail;
}

/*
 * Return the first element and remove it from q.
 * - q must be non-empty.
 */
extern int32_t int_queue_pop(int_queue_t *q);


/*
 * Get the first element of q but don't remove it.
 * - q must be non-empty
 */
extern int32_t int_queue_first(int_queue_t *q);


/*
 * Get the last element of q (don't remove it)
 * - q must be non-empty
 */
extern int32_t int_queue_last(int_queue_t *q);


/*
 * Empty the queue
 */
static inline void int_queue_reset(int_queue_t *q) {
  q->head = 0;
  q->tail = 0;
}


#endif /* __INT_QUEUES_H */
