/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test map; int32 -> uint8
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#include "utils/mark_vectors.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Print content
 */
static void print_mark_vector(mark_vector_t *v) {
  uint32_t i, n;

  printf("mark vector %p\n", v);
  printf("  size = %"PRIu32"\n", v->size);
  printf("  end_map = %"PRIu32"\n", v->end_map);
  printf("  default = %"PRIu8"\n", v->def);

  n = v->end_map;
  if (n > 0) {
    printf("  content:\n");
    for (i=0; i<n; i++) {
      if (v->map[i] != v->def) {
	printf("   map[%"PRIu32"] = %"PRIu8"\n", i, v->map[i]);
      }
    }
  } else {
    printf("  empty map\n");
  }
  printf("\n");
}


/*
 * Global vector
 */
static mark_vector_t vector;


/*
 * Test 1: default value = 0
 */
static void test1(void) {
  int32_t i;

  printf("\nTEST1\n\n");

  init_mark_vector(&vector, 0, 0);
  printf("After init\n");
  print_mark_vector(&vector);

  printf("add 0 --> 7\n");
  mark_vector_add_mark(&vector, 0, 7);
  print_mark_vector(&vector);;

  printf("add 30 --> 5\n");
  mark_vector_add_mark(&vector, 30, 5);
  print_mark_vector(&vector);

  printf("add 12 --> 1\n");
  mark_vector_add_mark(&vector, 12, 1);
  print_mark_vector(&vector);

  printf("add 33 --> 6\n");
  mark_vector_add_mark(&vector, 33, 6);
  print_mark_vector(&vector);

  printf("Check map\n");
  for (i=0; i<40; i++) {
    printf("  map[%"PRId32"] = %"PRIu8"\n", i, mark_vector_get_mark(&vector, i));
  }
  printf("\n");

  assert(mark_vector_get_mark(&vector, 33) == 6);
  assert(mark_vector_get_mark(&vector, 12) == 1);
  assert(mark_vector_get_mark(&vector, 30) == 5);
  assert(mark_vector_get_mark(&vector, 0) == 7);

  reset_mark_vector(&vector);
  printf("After reset\n");
  print_mark_vector(&vector);

  printf("add 10 --> 1\n");
  mark_vector_add_mark(&vector, 10, 1);
  printf("add 20 --> 2\n");
  mark_vector_add_mark(&vector, 20, 2);
  printf("add 39 --> 3\n");
  mark_vector_add_mark(&vector, 39, 3);
  print_mark_vector(&vector);

  printf("Check map\n");
  for (i=0; i<40; i++) {
    printf("  map[%"PRId32"] = %"PRIu8"\n", i, mark_vector_get_mark(&vector, i));
  }
  printf("\n");

  assert(mark_vector_get_mark(&vector, 10) == 1);
  assert(mark_vector_get_mark(&vector, 20) == 2);
  assert(mark_vector_get_mark(&vector, 39) == 3);

  delete_mark_vector(&vector);
}


/*
 * Test 2: n random additions
 */
static void test2(uint32_t n) {
  uint32_t i;
  int32_t j;
  uint8_t x;

  printf("\nTEST2\n\n");
  init_mark_vector(&vector, 20, 255);
  printf("After init\n");
  print_mark_vector(&vector);

  for (i=0; i<n; i++) {
    j = (int32_t) (random() % 2000);
    x = (uint8_t) (random() & 0xFF);

    printf("add %"PRId32" --> %"PRIu8"\n", j, x);
    mark_vector_add_mark(&vector, j, x);

    assert(mark_vector_get_mark(&vector, j) == x);
  }

  print_mark_vector(&vector);

  delete_mark_vector(&vector);
}

int main() {
  test1();
  test2(20);
  test2(10000);

  return 0;
}
