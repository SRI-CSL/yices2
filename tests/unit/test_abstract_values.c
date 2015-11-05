/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the abstract object modules
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "model/abstract_values.h"
#include "terms/types.h"

static type_table_t types;
static pstore_t store;


/*
 * Print particle x
 */
static void print_particle(particle_t x) {
  particle_tuple_t *tup;
  uint32_t i, n;

  switch (particle_kind(&store, x)) {
  case LABEL_PARTICLE:
    printf("(lab %"PRId32")", particle_label(&store, x));
    break;
  case FRESH_PARTICLE:
    printf("(fresh tau!%"PRId32")", fresh_particle_type(&store, x));
    break;
  case TUPLE_PARTICLE:
    tup = tuple_particle_desc(&store, x);
    printf("(tuple");
    n = tup->nelems;
    for (i=0; i<n; i++) {
      if (is_fresh_particle(&store, tup->elem[i])) {
	printf(" p!%"PRId32, tup->elem[i]);
      } else {
	printf(" ");
	print_particle(tup->elem[i]);
      }
    }
    printf(")");
    break;
  }
}

/*
 * Print p[x] = ...
 */
static void print_particle_def(particle_t x) {
  printf(" p!%"PRId32" = ", x);
  print_particle(x);
  printf("\n");
}


/*
 * Print array content
 */
static void print_particle_array(particle_t *q, uint32_t n) {
  uint32_t i;

  printf("[");
  for (i=0; i<n; i++) {
    if (i > 0) {
      printf(" ");
    }
    printf("p!%"PRId32, q[i]);
  }
  printf("]");
}


/*
 * Print all objects in set
 */
static void print_particle_set(particle_set_t *set) {
  uint32_t i, n;

  if (set == NULL) {
    printf("null set\n");
  } else {
    printf("set[");
    n = set->arity;
    for (i=0; i<n; i++) {
      if (i>0) {
	printf(", ");
      }
      printf("tau!%"PRId32, set->type[i]);
    }
    printf("] = {");
    n = set->nelems;
    for (i=0; i<n; i++) {
      if (i>0) {
	printf(", ");
      }
      printf("p!%"PRId32, set->data[i]);
    }
    printf("}\n");
    for (i=0; i<n; i++) {
      print_particle_def(set->data[i]);
    }
  }
}



/*
 * Test1: elements of a scalar type
 */
static void test1(void) {
  type_t tau;
  particle_t a, b, c;
  particle_t q[40], x;
  uint32_t n;

  printf("\n"
         "***********************\n"
	 "*       TEST 1        *\n"
         "***********************\n");

  tau = new_scalar_type(&types, 8);
  a = pstore_labeled_particle(&store, 32, tau);
  b = pstore_labeled_particle(&store, 34, tau);
  c = pstore_fresh_particle(&store, tau);

  printf("\nInitial objects of type tau!%"PRId32"\n", tau);
  print_particle_def(a);
  print_particle_def(b);
  print_particle_def(c);
  printf("\n");

  // array a, c
  q[0] = a;
  q[1] = c;
  printf("Test array: ");
  print_particle_array(q, 2);
  printf("\n");

  // create new objects until that fails
  n = 2;
  x = get_distinct_particle(&store, tau, n, q);
  while (x != null_particle) {
    printf("New particle:");
    print_particle_def(x);
    q[n] = x;
    n ++;
    assert(n <= 40);
    x = get_distinct_particle(&store, tau, n, q);
  }

  printf("\nSaturation\n");
  print_particle_set(pstore_find_set_for_type(&store, tau));
  printf("\n\n");
}



/*
 * Test2: elements of an uninterpreted type
 */
static void test2(void) {
  type_t tau;
  particle_t a, b, c;
  particle_t q[40], x;
  uint32_t n;

  printf("\n"
         "***********************\n"
	 "*       TEST 2        *\n"
         "***********************\n");

  tau = new_uninterpreted_type(&types);
  a = pstore_labeled_particle(&store, 100, tau);
  b = pstore_labeled_particle(&store, 102, tau);
  c = pstore_fresh_particle(&store, tau);

  printf("\nInitial objects of type tau!%"PRId32"\n", tau);
  print_particle_def(a);
  print_particle_def(b);
  print_particle_def(c);
  printf("\n");

  // Initial array: empty
  printf("Test array: ");
  print_particle_array(q, 0);
  printf("\n");

  // create new objects until that fails
  for (n = 0; n<40; n++) {
    x = get_distinct_particle(&store, tau, n, q);
    printf("New particle:");
    print_particle_def(x);
    q[n] = x;
  }

  printf("\nFinal set\n");
  print_particle_set(pstore_find_set_for_type(&store, tau));
  printf("\n\n");
}



/*
 * Test 3: triples of booleans
 */
static void test3(void) {
  type_t tau[3];
  particle_t a, b;
  particle_t q[40], x;
  uint32_t n;

  printf("\n"
         "***********************\n"
	 "*       TEST 3        *\n"
         "***********************\n");

  tau[0] = bool_type(&types);
  tau[1] = bool_type(&types);
  tau[2] = bool_type(&types);

  // a=true, b=false
  a = pstore_labeled_particle(&store, 0, tau[0]);
  b = pstore_labeled_particle(&store, 1, tau[0]);

  printf("\nInitial objects of type tau!%"PRId32"\n", tau[0]);
  print_particle_def(a);
  print_particle_def(b);
  printf("\n");

  // Initial array: empty
  printf("Test array: ");
  print_particle_array(q, 0);
  printf("\n");

  // create new tuples until that fails
  for (n = 0; n<40; n++) {
    x = get_distinct_tuple(&store, 3, tau, n, q);
    if (x == null_particle) {
      printf("Saturation\n");
      break;
    }
    printf("New particle:");
    print_particle_def(x);
    q[n] = x;
  }

  printf("\nFinal set\n");
  print_particle_set(pstore_find_set_for_types(&store, 3, tau));
  printf("\n\n");

}



/*
 * Test 4: pairs (scalar6 x bool)
 * - start with scalar6 empty
 * - if test3 is called first, bool is saturated
 */
static void test4(void) {
  type_t tau[2];
  particle_t q[40], x;
  uint32_t n;

  printf("\n"
         "***********************\n"
	 "*       TEST 4        *\n"
         "***********************\n");

  tau[0] = new_scalar_type(&types, 6);
  tau[1] = bool_type(&types);

  // Initial array: empty
  printf("Test array: ");
  print_particle_array(q, 0);
  printf("\n");

  // create new tuples until that fails
  for (n = 0; n<40; n++) {
    x = get_distinct_tuple(&store, 2, tau, n, q);
    if (x == null_particle) {
      printf("Saturation\n");
      break;
    }
    printf("New particle:");
    print_particle_def(x);
    q[n] = x;
  }

  printf("\nFinal sets\n");
  print_particle_set(pstore_find_set_for_type(&store, tau[0]));
  printf("\n");
  print_particle_set(pstore_find_set_for_type(&store, tau[1]));
  printf("\n");
  print_particle_set(pstore_find_set_for_types(&store, 2, tau));
  printf("\n\n");

}


/*
 * Test 5: pairs (int x int)
 * - start with pairs [4, 4], [6, 6]
 */
static void test5(void) {
  type_t tau[2];
  particle_t a, b, c, d;
  particle_t q[40], x;
  uint32_t n;

  printf("\n"
         "***********************\n"
	 "*       TEST 5        *\n"
         "***********************\n");

  tau[0] = int_type(&types);
  tau[1] = int_type(&types);

  a = pstore_labeled_particle(&store, 4, tau[0]);
  b = pstore_labeled_particle(&store, 6, tau[1]);

  q[0] = a;
  q[1] = a;
  c = pstore_tuple_particle(&store, 2, q, tau);

  q[0] = b;
  q[1] = b;
  d = pstore_tuple_particle(&store, 2, q, tau);

  printf("\nInitial objects of type tau!%"PRId32"\n", tau[0]);
  print_particle_def(a);
  print_particle_def(b);
  printf("\n");

  printf("Initial objects of type tau!%"PRId32" x tau!%"PRId32"\n", tau[0], tau[1]);
  print_particle_def(c);
  print_particle_def(d);
  printf("\n");

  printf("\nInitial sets\n");
  print_particle_set(pstore_find_set_for_type(&store, tau[0]));
  printf("\n");
  print_particle_set(pstore_find_set_for_types(&store, 2, tau));
  printf("\n\n");


    // Initial array: empty
  printf("Test array: ");
  print_particle_array(q, 0);
  printf("\n");

  // create new tuples until that fails
  for (n = 0; n<40; n++) {
    x = get_distinct_tuple(&store, 2, tau, n, q);
    if (x == null_particle) {
      printf("Saturation\n");
      break;
    }
    printf("New particle:");
    print_particle_def(x);
    q[n] = x;
  }

  printf("\nFinal sets\n");
  print_particle_set(pstore_find_set_for_type(&store, tau[0]));
  printf("\n");
  print_particle_set(pstore_find_set_for_types(&store, 2, tau));
  printf("\n\n");


}


/*
 * Test 6: pairs (real x real)
 * - start with pairs [9, 11], [11, 9]
 */
static void test6(void) {
  type_t tau[2];
  particle_t a, b, c, d;
  particle_t q[40], x;
  uint32_t n;

  printf("\n"
         "***********************\n"
	 "*       TEST 6        *\n"
         "***********************\n");

  tau[0] = real_type(&types);
  tau[1] = real_type(&types);

  a = pstore_labeled_particle(&store, 9, tau[0]);
  b = pstore_labeled_particle(&store, 11, tau[1]);

  q[0] = b;
  q[1] = a;
  c = pstore_tuple_particle(&store, 2, q, tau);

  q[0] = a;
  q[1] = b;
  d = pstore_tuple_particle(&store, 2, q, tau);

  printf("\nInitial objects of type tau!%"PRId32"\n", tau[0]);
  print_particle_def(a);
  print_particle_def(b);
  printf("\n");

  printf("Initial objects of type tau!%"PRId32" x tau!%"PRId32"\n", tau[0], tau[1]);
  print_particle_def(c);
  print_particle_def(d);
  printf("\n");

  printf("\nInitial sets\n");
  print_particle_set(pstore_find_set_for_type(&store, tau[0]));
  printf("\n");
  print_particle_set(pstore_find_set_for_types(&store, 2, tau));
  printf("\n\n");


    // Initial array: empty
  printf("Test array: ");
  print_particle_array(q, 0);
  printf("\n");

  // create new tuples until that fails
  for (n = 0; n<40; n++) {
    x = get_distinct_tuple(&store, 2, tau, n, q);
    if (x == null_particle) {
      printf("Saturation\n");
      break;
    }
    printf("New particle:");
    print_particle_def(x);
    q[n] = x;
  }

  printf("\nFinal sets\n");
  print_particle_set(pstore_find_set_for_type(&store, tau[0]));
  printf("\n");
  print_particle_set(pstore_find_set_for_types(&store, 2, tau));
  printf("\n\n");


}



int main(void) {
  init_type_table(&types, 10);
  init_pstore(&store, &types);

  test1();
  test2();
  test3();
  test4();
  test5();
  test6();

  delete_pstore(&store);
  delete_type_table(&types);

  return 0;
}
