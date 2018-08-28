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
 * QUEUE OF MERGE_DATA
 */

#include <assert.h>

#include "merge_queue.h"
#include "utils/memalloc.h"

/*
 * Maximal size: make sure n * sizeof(int32_t) does not overflow
 */
#define MAX_MERGE_QUEUE_SIZE (UINT32_MAX/sizeof(int32_t))

/*
 * Default size
 */
#define DEFAULT_MERGE_QUEUE_INITIAL_SIZE 16

/*
 * Initialize a queue of size n
 */
void init_merge_queue(merge_queue_t *q, uint32_t n) {
  if (n == 0) {
    n = DEFAULT_MERGE_QUEUE_INITIAL_SIZE;
  } else if (n > MAX_MERGE_QUEUE_SIZE) {
    out_of_memory();
  }
  q->data = (merge_data_t*) safe_malloc(n * sizeof(merge_data_t));
  q->size = n;
  q->head = 0;
  q->tail = 0;
}


/*
 * Delete: free data array
 */
void delete_merge_queue(merge_queue_t *q) {
  safe_free(q->data);
  q->data = NULL;
}


/*
 * Resize the queue. make data array 50% larger.
 * content of data array is unchanged
 */
static void resize_queue(merge_queue_t *q) {
  uint32_t n;

  n = q->size + 1;
  n += n >> 1;

  if (n > MAX_MERGE_QUEUE_SIZE) {
    out_of_memory();
  }

  q->data = (merge_data_t*) safe_realloc(q->data, n * sizeof(merge_data_t));
  q->size = n;
}



/*
 * Push element x at the end of the queue
 */
merge_data_t* merge_queue_push(merge_queue_t *q) {
  uint32_t i, n, j;

  i = q->tail;
  i ++;
  q->tail = i;

  if (i == q->size) {
    if (q->head == 0) {
      /*
       * full queue, stored in data[0...size-1],
       * just increase the size
       */
      resize_queue(q);
    } else {
      q->tail = 0;
    }
  } else if (i == q->head) {
    /*
     * full queue, stored in data[0..i-1][head .. size-1]
     * increase the size and shift data[head .. size - 1] to the end
     * of the new data array.
     */
    n = q->size;
    resize_queue(q);
    j = q->size;
    do {
      n --;
      j --;
      q->data[j] = q->data[n];
    } while (n > i);
    q->head = j;
  }

  return q->data + i - 1;
}

void merge_queue_push_init(merge_queue_t *q, eq_node_id_t lhs, eq_node_id_t rhs,
    eq_reason_type_t reason_type, uint32_t reason_data) {
  merge_data_t* new_merge = merge_queue_push(q);
  new_merge->lhs = lhs;
  new_merge->rhs = rhs;
  new_merge->reason.type = reason_type;
  new_merge->reason.data = reason_data;
}


/*
 * Return first element and remove it
 */
void merge_queue_pop(merge_queue_t *q) {
  uint32_t h;

  assert(q->head != q->tail);

  h = q->head;
  h ++;
  if (h >= q->size) h = 0;
  q->head = h;
}



/*
 * Get the first element (don't remove it).
 */
merge_data_t* merge_queue_first(merge_queue_t *q) {
  assert(q->head != q->tail);
  return q->data + q->head;
}


/*
 * Get the last element (don't remove it)
 */
merge_data_t* merge_queue_last(merge_queue_t *q) {
  uint32_t i;

  assert(q->head != q->tail);
  i = q->tail;
  if (i == 0) {
    i = q->size;
  }
  assert(i > 0);
  return q->data + (i-1);
}
