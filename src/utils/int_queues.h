/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * QUEUES OF 32BIT SIGNED INTEGERS
 */

#ifndef __INT_QUEUES_H
#define __INT_QUEUES_H

#include <stdint.h>
#include <stdbool.h>


/**
 * Components:
 * - data = integer array to store the elements
 * - capacity = size of that array
 * - head, tail = indices between 0 and size - 1.
 * The queue is managed as a circular array:
 * - if head = tail, the queue is empty
 * - if head < tail, the queue content is data[head ... tail-1]
 * - if head > tail, the queue content is
 *     data[head...capacity-1] + data[0 ... tail-1]
 */
typedef struct int_queue_s {
  int32_t *data;
  uint32_t capacity;
  uint32_t head;
  uint32_t tail;
} int_queue_t;


/**
 * Maximal size: make sure n * sizeof(int32_t) does not overflow
 */
#define MAX_INT_QUEUE_CAPACITY (UINT32_MAX/sizeof(int32_t))


/**
 * Default size
 */
#define DEFAULT_INT_QUEUE_INITIAL_CAPACITY 16


/**
 * Initialize a queue of size n.
 * If n = 0 then DEFAULT_QUEUE_INITIAL_SIZE is used.
 */
void init_int_queue(int_queue_t *q, uint32_t n);


/**
 * Delete q
 */
void delete_int_queue(int_queue_t *q);


/**
 * Push element x in the queue (at the end)
 */
void int_queue_push(int_queue_t *q, int32_t x);


/**
 * Push a[0 ... n-1] in the queue (in this order)
 */
void int_queue_push_array(int_queue_t *q, int32_t *a, uint32_t n);


/**
 * Check whether the queue is empty
 */
static inline bool int_queue_is_empty(int_queue_t *q) {
  return q->head == q->tail;
}


/**
 * Gets the size of the queue.
 */
uint32_t int_queue_size(const int_queue_t *q);


/**
 * Return the first element and remove it from q.
 * - q must be non-empty.
 */
int32_t int_queue_pop(int_queue_t *q);


/**
 * Get the first element of q but don't remove it.
 * - q must be non-empty
 */
int32_t int_queue_first(const int_queue_t *q);


/**
 * Get the last element of q (don't remove it)
 * - q must be non-empty
 */
int32_t int_queue_last(const int_queue_t *q);


/**
 * Gets the element at position i
 */
int32_t int_queue_at(const int_queue_t *q, uint32_t i);


/**
 * Empty the queue
 */
static inline
void int_queue_reset(int_queue_t *q) {
  q->head = 0;
  q->tail = 0;
}

/**
 * Swaps two queues
 */
void int_queue_swap(int_queue_t *q1, int_queue_t *q2);

#endif /* __INT_QUEUES_H */
