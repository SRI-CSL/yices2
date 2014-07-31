/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "solvers/egraph/egraph_assertion_queues.h"

static eassertion_queue_t queue;


/*
 * Buffer for building distinct assertions
 */
#define BUFFER_SIZE 400
static int32_t buffer[BUFFER_SIZE];

/*
 * Array of composites to use as pointers
 */
#define NUM_COMPOSIDES 20
static composite_t fake[20];


/*
 * Store n variables in bufer, all are set to k
 */
static void set_buffer(uint32_t n, int32_t k) {
  uint32_t i;

  for (i=0; i<n; i++) {
    buffer[i] = k;
  }
}



/*
 * Convert an assertion type to a string
 */
static char *kind2string(eassertion_kind_t k) {
  switch (k) {
  case EGRAPH_VAR_EQ:
    return "eq";
  case EGRAPH_VAR_DISEQ:
    return "diseq";
  case EGRAPH_VAR_DISTINCT:
    return "distinct";
  default:
    return "ERROR";
  }
}


/*
 * Print an assertion a
 */
static void print_assertion(eassertion_t *a) {
  uint32_t i, n, size;

  n = eassertion_get_arity(a);
  size = eassertion_get_size(a);
  printf("Assertion %p: %s, arith = %"PRIu32", size = %"PRIu32"\n", a, kind2string(eassertion_get_kind(a)), n, size);
  printf(" hint = %p\n", a->hint);
  printf(" id = %"PRId32"\n", a->id);
  printf(" vars:");
  for (i=0; i<n; i++) {
    printf(" %"PRId32, a->var[i]);
  }
  printf("\n");
}


/*
 * Print the queue content
 */
static void print_queue(void) {
  eassertion_t *a, *end;

  a = eassertion_queue_start(&queue);
  end = eassertion_queue_end(&queue);
  while (a < end) {
    print_assertion(a);
    a = eassertion_next(a);
  }
  printf("---\n");
}


/*
 * Test queue
 */
int main() {
  uint32_t i, n;

  init_eassertion_queue(&queue);

  printf("=== Initial queue ===\n");
  print_queue();

  eassertion_push_eq(&queue, 1, 1, 1);
  eassertion_push_eq(&queue, 2, 2, 2);
  eassertion_push_eq(&queue, 3, 3, 3);
  eassertion_push_eq(&queue, 4, 4, 4);
  eassertion_push_eq(&queue, 5, 5, 5);
  eassertion_push_eq(&queue, 6, 6, 6);
  printf("=== After 6 eqs ===\n");
  print_queue();

  reset_eassertion_queue(&queue);
  printf("=== After reset ===\n");
  print_queue();

  eassertion_push_diseq(&queue, 1, 1, fake);
  eassertion_push_diseq(&queue, 2, 2, fake + 1);
  eassertion_push_diseq(&queue, 3, 3, fake + 2);
  eassertion_push_diseq(&queue, 4, 4, fake + 3);
  eassertion_push_diseq(&queue, 5, 5, fake + 4);
  eassertion_push_diseq(&queue, 6, 6, fake + 5);
  printf("=== After 6 diseqs ===\n");
  print_queue();

  n = 0;
  for (i=0; i<300; i++) {
    set_buffer(100, i);
    eassertion_push_distinct(&queue, 100, buffer, NULL);
    n ++;
    if (n % 5 == 0) {
      printf("=== After %"PRIu32" distincts ===\n", n);
      print_queue();
    }
  }
  delete_eassertion_queue(&queue);

  return 0;
}
