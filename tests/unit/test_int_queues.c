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

#include <stdio.h>
#include <inttypes.h>

#include "utils/int_queues.h"

static int_queue_t q;

static void print_queue(int_queue_t *q) {
  uint32_t i;

  printf("queue %p\n", q);
  printf("  size = %"PRIu32"\n", q->capacity);
  printf("  head = %"PRIu32"\n", q->head);
  printf("  tail = %"PRIu32"\n", q->tail);
  printf("  content:");
  if (q->head < q->tail) {
    for (i=q->head; i<q->tail; i++) {
      printf(" %"PRId32, q->data[i]);
    }
    printf("\n");
  } else if (q->tail < q->head) {
    for (i=q->head; i<q->capacity; i++) {
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
  for (i=0; i<q->capacity; i++) printf(" %"PRId32, q->data[i]);
  printf("\n");
}

int main(void) {
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
