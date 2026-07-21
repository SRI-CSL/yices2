/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#include "equality_graph_types.h"

typedef struct merge_data_s {
  eq_node_id_t lhs;
  eq_node_id_t rhs;
  eq_reason_t reason;
} merge_data_t;

/*
 * Components:
 * - data = array of merge data
 * - size = size of that array
 * - head, tail = indices between 0 and size - 1.
 * The queue is managed as a circular array:
 * - if head = tail, the queue is empty
 * - if head < tail, the queue content is data[head ... tail-1]
 * - if head > tail, the queue content is
 *     data[head...size-1] + data[0 ... tail-1]
 */
typedef struct merge_queue_s {
  merge_data_t *data;
  uint32_t size;
  uint32_t head;
  uint32_t tail;
} merge_queue_t;


/*
 * Initialize a queue of size n.
 * If n = 0 then DEFAULT_QUEUE_INITIAL_SIZE is used.
 */
void init_merge_queue(merge_queue_t *q, uint32_t n);


/*
 * Delete q
 */
void delete_merge_queue(merge_queue_t *q);


/*
 * Push new element to the queue (at the end) and get reference to the
 * uninitialized element.
 */
merge_data_t* merge_queue_push(merge_queue_t *q);

/*
 * Push new element to the queue (at the end).
 */
void merge_queue_push_init(merge_queue_t *q, eq_node_id_t lhs, eq_node_id_t rhs,
    eq_reason_type_t reason_type, uint32_t reason_data);

/*
 * Check whether the queue is empty
 */
static inline bool merge_queue_is_empty(const merge_queue_t *q) {
  return q->head == q->tail;
}

/*
 * Remove first element from the front.
 * - q must be non-empty.
 */
void merge_queue_pop(merge_queue_t *q);


/*
 * Get the first element of q but don't remove it.
 * - q must be non-empty
 */
merge_data_t* merge_queue_first(merge_queue_t *q);


/*
 * Get the last element of q (don't remove it)
 * - q must be non-empty
 */
merge_data_t* merge_queue_last(merge_queue_t *q);


/*
 * Empty the queue
 */
static inline void merge_queue_reset(merge_queue_t *q) {
  q->head = 0;
  q->tail = 0;
}
