/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * QUEUES OF 32BIT SIGNED INTEGERS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/int_queues.h"


/*
 * Initialize a queue of size n
 */
void init_int_queue(int_queue_t *q, uint32_t n) {
  if (n == 0) {
    n = DEFAULT_INT_QUEUE_INITIAL_SIZE;
  } else if (n > MAX_INT_QUEUE_SIZE) {
    out_of_memory();
  }

  q->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
  q->size = n;
  q->head = 0;
  q->tail = 0;
}


/*
 * Delete: free data array
 */
void delete_int_queue(int_queue_t *q) {
  safe_free(q->data);
  q->data = NULL;
}


/*
 * Resize the queue. make data array 50% larger.
 * content of data array is unchanged
 */
static void resize_queue(int_queue_t *q) {
  uint32_t n;

  n = q->size + 1;
  n += n >> 1;

  if (n > MAX_INT_QUEUE_SIZE) {
    out_of_memory();
  }

  q->data = (int32_t *) safe_realloc(q->data, n * sizeof(int32_t));
  q->size = n;
}



/*
 * Push element x at the end of the queue
 */
void int_queue_push(int_queue_t *q, int32_t x) {
  uint32_t i, n, j;

  i = q->tail;
  q->data[i] = x;
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
}


/*
 * Push a[0 ... n-1] in the queue (in this order)
 */
void int_queue_push_array(int_queue_t *q, int32_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    int_queue_push(q, a[i]);
  }
}


/*
 * Return first element and remove it
 */
int32_t int_queue_pop(int_queue_t *q) {
  int32_t h, x;

  assert(q->head != q->tail);

  h = q->head;
  x = q->data[h];
  h ++;
  if (h >= q->size) h = 0;
  q->head = h;

  return x;
}



/*
 * Get the first element (don't remove it).
 */
int32_t int_queue_first(int_queue_t *q) {
  assert(q->head != q->tail);
  return q->data[q->head];
}


/*
 * Get the last element (don't remove it)
 */
int32_t int_queue_last(int_queue_t *q) {
  uint32_t i;

  assert(q->head != q->tail);
  i = q->tail;
  if (i == 0) {
    i = q->size;
  }
  assert(i > 0);
  return q->data[i-1];
}
