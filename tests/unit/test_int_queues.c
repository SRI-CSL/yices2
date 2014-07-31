/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/int_queues.h"

static int_queue_t q;

static void print_queue(int_queue_t *q) {
  uint32_t i;

  printf("queue %p\n", q);
  printf("  size = %"PRIu32"\n", q->size);
  printf("  head = %"PRIu32"\n", q->head);
  printf("  tail = %"PRIu32"\n", q->tail);
  printf("  content:");
  if (q->head < q->tail) {
    for (i=q->head; i<q->tail; i++) {
      printf(" %"PRId32, q->data[i]);
    }
    printf("\n");
  } else if (q->tail < q->head) {
    for (i=q->head; i<q->size; i++) {
      printf(" %"PRId32, q->data[i]);
    }
    for (i=0; i<q->tail; i++) {
      printf(" %"PRId32, q->data[i]);
    }
    printf("\n");
  } else {
    printf(" empty\n");
  }
}

static void print_queue_data(int_queue_t *q) {
  uint32_t i;
  printf("head = %"PRIu32", tail = %"PRIu32"\n", q->head, q->tail);
  printf("data:");
  for (i=0; i<q->size; i++) printf(" %"PRId32, q->data[i]);
  printf("\n");
}

int main() {
  int32_t x;

  init_int_queue(&q, 2);
  print_queue(&q);

  printf("\nadding elements 1, 2\n");
  int_queue_push(&q, 1);
  int_queue_push(&q, 2);
  print_queue(&q);

  printf("\nremoving elements\n");
  while (! int_queue_is_empty(&q)) {
    x = int_queue_pop(&q);
    printf("%"PRId32" ", x);
  }
  printf("\n");

  print_queue(&q);

  for (x=1; x<=100; x++) {
    printf("\nadding element %"PRId32"\n", x);
    int_queue_push(&q, x);
    print_queue_data(&q);
  }

  printf("\n");
  print_queue(&q);

  printf("\nremoving elements\n");
  while (! int_queue_is_empty(&q)) {
    x = int_queue_pop(&q);
    printf("%"PRId32" ", x);
  }
  printf("\n");

  print_queue(&q);

  delete_int_queue(&q);

  return 0;
}
