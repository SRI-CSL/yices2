/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * QUEUES OF POINTERS
 *
 * data = content of the queue
 * size = full size of the data array
 * head = start of the queue = index in data array
 * tail = end of the queue = index in data array
 *
 * There are two modes:
 * 1) if 0 <= head <= tail < size, then
 *    the queue consists of data[head ... tail-1]
 *    the queue is empty if head = tail
 * 2) if 0 <= tail < head < size then
 *    the queue is the concatenation of
 *    data[head ... size -1] and data[0 ... tail-1]
 *
 * So size cannot be zero and head and tail are always between
 * 0 and size-1.
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/ptr_queues.h"


/*
 * Initialize a queue of size n
 */
void init_ptr_queue(ptr_queue_t *q, uint32_t n) {
  if (n == 0) n = DEF_PTR_QUEUE_SIZE;
  if (n > MAX_PTR_QUEUE_SIZE) {
    out_of_memory();
  }

  q->data = (void **) safe_malloc(n * sizeof(void *));
  q->size = n;
  q->head = 0;
  q->tail = 0;
}


/*
 * Delete: free data array
 */
void delete_ptr_queue(ptr_queue_t *q) {
  safe_free(q->data);
  q->data = NULL;
}


/*
 * Resize the queue. Make the data array 50% larger.
 * The array's content is unchanged.
 */
static void resize_queue(ptr_queue_t *q) {
  uint32_t n;

  n = q->size + 1;
  n += n >> 1;

  if (n > MAX_PTR_QUEUE_SIZE) {
    out_of_memory();
  }

  q->data = (void **) safe_realloc(q->data, n * sizeof(void *));
  q->size = n;
}



/*
 * Push element p at the end of the queue
 */
void ptr_queue_push(ptr_queue_t *q, void *p) {
  uint32_t i, n, j;

  i = q->tail;
  q->data[i] = p;
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
    assert(n < j);
    do {
      n --;
      j --;
      q->data[j] = q->data[n];
    } while (n > i);
    q->head = j;
  }
}


/*
 * Return first element and remove it
 */
void *ptr_queue_pop(ptr_queue_t *q) {
  uint32_t h;
  void *x;

  assert(q->head != q->tail);

  h = q->head;
  x = q->data[h];
  h ++;
  if (h >= q->size) h = 0;
  q->head = h;

  return x;
}



/*
 * First element of q
 */
void *ptr_queue_first(ptr_queue_t *q) {
  assert(q->head != q->tail);
  return q->data[q->head];
}


/*
 * Last element of q
 */
void *ptr_queue_last(ptr_queue_t *q) {
  uint32_t i;

  assert(q->head != q->tail);
  i = q->tail;
  if (i == 0) {
    i = q->size;
  }
  assert(i > 0);
  return q->data[i-1];
}
