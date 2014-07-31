/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * QUEUES OF POINTERS
 */

#ifndef __PTR_QUEUES_H
#define __PTR_QUEUES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Components:
 * - data = integer array to store the pointers
 * - size = size of that array
 * - head, tail = indices between 0 and size - 1.
 * The queue is managed as a circular array:
 * - if head = tail, the queue is empty
 * - if head < tail, queue content is data[head ... tail-1]
 * - if head > tail, queue content is
 *     data[head...size-1] + data[0 ... tail-1]
 */
typedef struct ptr_queue_s {
  void **data;
  uint32_t size;
  uint32_t head;
  uint32_t tail;
} ptr_queue_t;


#define DEF_PTR_QUEUE_SIZE 16
#define MAX_PTR_QUEUE_SIZE (UINT32_MAX/sizeof(void *))


/*
 * Initialize a queue of size n.
 * If n = 0 then the default size is used
 */
extern void init_ptr_queue(ptr_queue_t *q, uint32_t n);


/*
 * Delete q
 */
extern void delete_ptr_queue(ptr_queue_t *q);


/*
 * Push element p in the queue (at the end)
 */
extern void ptr_queue_push(ptr_queue_t *q, void *p);


/*
 * Check whether the queue is empty
 */
static inline bool ptr_queue_is_empty(ptr_queue_t *q) {
  return q->head == q->tail;
}

/*
 * Return the first element and remove it from q.
 * - q must be non-empty.
 */
extern void *ptr_queue_pop(ptr_queue_t *q);


/*
 * Get the first element or last element (don't remove it)
 * - q must be non-empty
 */
extern void *ptr_queue_first(ptr_queue_t *q);
extern void *ptr_queue_last(ptr_queue_t *q);


/*
 * Empty the queue
 */
static inline void ptr_queue_reset(ptr_queue_t *q) {
  q->head = 0;
  q->tail = 0;
}


#endif /* __PTR_QUEUES_H */
