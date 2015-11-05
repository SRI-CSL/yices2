/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the map tree module
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "model/abstract_values.h"
#include "model/fun_maps.h"
#include "model/fun_trees.h"
#include "terms/types.h"

static type_table_t types;
static pstore_t store;
static fun_tree_t tree;



/*
 * Print particle x as a index (or tuple)
 */
static void print_index(particle_t x) {
  particle_tuple_t *tup;
  uint32_t i, n;

  switch (particle_kind(&store, x)) {
  case LABEL_PARTICLE:
    printf("L%"PRId32, particle_label(&store, x));
    break;
  case FRESH_PARTICLE:
    printf("p!%"PRId32, x);
    break;
  case TUPLE_PARTICLE:
    tup = tuple_particle_desc(&store, x);
    n = tup->nelems;
    for (i=0; i<n; i++) {
      if (i>0) printf(" ");
      print_index(tup->elem[i]);
    }
    break;
  }
}


/*
 * Print particle x as a value
 */
static void print_value(particle_t x) {
  particle_tuple_t *tup;
  uint32_t i, n;

  switch (particle_kind(&store, x)) {
  case LABEL_PARTICLE:
    printf("L%"PRId32, particle_label(&store, x));
    break;
  case FRESH_PARTICLE:
    printf("p!%"PRId32, x);
    break;
  case TUPLE_PARTICLE:
    tup = tuple_particle_desc(&store, x);
    printf("(tuple ");
    n = tup->nelems;
    for (i=0; i<n; i++) {
      printf(" ");
      print_value(tup->elem[i]);
    }
    printf(")");
    break;
  }
}


/*
 * Print a map
 */
static void print_map(map_t *map) {
  uint32_t i, n;
  particle_t idx, v;
  bool vmode;

  printf("map[%p]", map);
  n = map->nelems;
  vmode = n>=5; // vmode means one map per line

  for (i=0; i<n; i++) {
    idx = map->data[i].index;
    v = map->data[i].value;
    if (vmode) {
      printf("\n   ");
    } else if (i == 0) {
      printf(": ");
    } else {
      printf(", ");
    }
    print_index(idx);
    printf(" -> ");
    print_value(v);
  }

  v = map_default_value(map);
  if (v != null_particle) {
    if (vmode) {
      printf("\n   ");
    } else if (i == 0) {
      printf(": ");
    } else {
      printf(", ");
    }
    printf("def -> ");
    print_value(v);
  }

  printf("\n");
}



/*
 * Create type tau1 -> tau2
 */
static type_t fun_type1(type_t tau1, type_t tau2) {
  return function_type(&types, tau2, 1, &tau1);
}

/*
 * Create type tau1 x tau2 -> tau3
 */
static type_t fun_type2(type_t tau1, type_t tau2, type_t tau3) {
  type_t aux[2];

  aux[0] = tau1;
  aux[1] = tau2;
  return function_type(&types, tau3, 2, aux);
}



/*
 * Build 4 fully specified boolean maps and add them
 * to the tree
 */
static void test1(void) {
  particle_t tt, ff;
  map_t *map[5];
  type_t tau;
  bool ok;
  uint32_t i;

  printf("\n"
         "***********************\n"
	 "*       TEST 1        *\n"
         "***********************\n");

  tau = bool_type(&types);
  tt = pstore_labeled_particle(&store, 0, tau);
  ff = pstore_labeled_particle(&store, 1, tau);

  map[0] = new_map(3);
  set_map_default(map[0], ff);
  add_elem_to_map(map[0], ff, ff);
  add_elem_to_map(map[0], tt, ff);
  normalize_map(map[0]);

  map[1] = new_map(3);
  set_map_default(map[1], ff);
  add_elem_to_map(map[1], ff, ff);
  add_elem_to_map(map[1], tt, tt);
  normalize_map(map[1]);

  map[2] = new_map(3);
  set_map_default(map[2], ff);
  add_elem_to_map(map[2], ff, tt);
  add_elem_to_map(map[2], tt, ff);
  normalize_map(map[2]);

  map[3] = new_map(3);
  set_map_default(map[3], ff);
  add_elem_to_map(map[3], ff, tt);
  add_elem_to_map(map[3], tt, tt);
  normalize_map(map[3]);

  // map[4] equal to map[2]. Different default
  map[4] = new_map(3);
  set_map_default(map[4], tt);
  add_elem_to_map(map[4], ff, tt);
  add_elem_to_map(map[4], tt, ff);
  normalize_map(map[4]);

  // print all the maps;
  printf("\nIinitial maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // prepare the tree
  tau = fun_type1(tau, tau); // [bool -> bool]
  reset_fun_tree(&tree);
  set_fun_tree_type(&tree, function_type_desc(&types, tau));

  // add all maps
  for (i=0; i<5; i++) {
    printf("adding map[%"PRIu32"]: ", i);
    fflush(stdout);
    ok = fun_tree_add_map(&tree, map[i]);
    if (ok) {
      printf("OK\n");
    } else {
      printf("Conflict\n");
    }
  }

  // print all the maps;
  printf("\nFinal maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // cleanup
  reset_fun_tree(&tree);
  for (i=0; i<5; i++) {
    free_map(map[i]);
  }

}


/*
 * Build 5 empty boolean maps and add them
 * to the tree. The last addition should fail.
 */
static void test2(void) {
  particle_t tt, ff;
  map_t *map[5];
  type_t tau;
  bool ok;
  uint32_t i;

  printf("\n"
         "***********************\n"
	 "*       TEST 2        *\n"
         "***********************\n");

  tau = bool_type(&types);
  tt = pstore_labeled_particle(&store, 0, tau);
  ff = pstore_labeled_particle(&store, 1, tau);

  // all maps are empty, with a default value
  map[0] = new_map(1);
  set_map_default(map[0], ff);
  normalize_map(map[0]);

  map[1] = new_map(1);
  set_map_default(map[1], tt);
  normalize_map(map[1]);

  map[2] = new_map(1);
  set_map_default(map[2], ff);
  normalize_map(map[2]);

  map[3] = new_map(1);
  set_map_default(map[3], tt);
  normalize_map(map[3]);

  map[4] = new_map(1);
  set_map_default(map[4], ff);
  normalize_map(map[4]);

  // print all the maps;
  printf("\nIinitial maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // prepare the tree
  tau = fun_type1(tau, tau); // [bool -> bool]
  reset_fun_tree(&tree);
  set_fun_tree_type(&tree, function_type_desc(&types, tau));

  // add all maps
  for (i=0; i<5; i++) {
    printf("adding map[%"PRIu32"]: ", i);
    fflush(stdout);
    ok = fun_tree_add_map(&tree, map[i]);
    if (ok) {
      printf("OK\n");
    } else {
      printf("Conflict\n");
    }
  }


  // print all the maps;
  printf("\nFinal maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // cleanup
  reset_fun_tree(&tree);
  for (i=0; i<5; i++) {
    free_map(map[i]);
  }

}



/*
 * Build 5 empty maps of type [U -> bool] and add them to the tree.
 * Use an infinite domain so all additions should succeed.
 */
static void test3(void) {
  particle_t ff;
  map_t *map[5];
  type_t unint, tau;
  bool ok;
  uint32_t i;

  printf("\n"
         "***********************\n"
	 "*       TEST 3        *\n"
         "***********************\n");

  tau = bool_type(&types);
  ff = pstore_labeled_particle(&store, 1, tau);

  // all maps have default false
  map[0] = new_map(1);
  set_map_default(map[0], ff);
  normalize_map(map[0]);

  map[1] = new_map(1);
  set_map_default(map[1], ff);
  normalize_map(map[1]);

  map[2] = new_map(1);
  set_map_default(map[2], ff);
  normalize_map(map[2]);

  map[3] = new_map(1);
  set_map_default(map[3], ff);
  normalize_map(map[3]);

  map[4] = new_map(1);
  set_map_default(map[4], ff);
  normalize_map(map[4]);

  // print all the maps;
  printf("\nIinitial maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // prepare the tree
  unint = new_uninterpreted_type(&types);
  tau = fun_type1(unint, tau); // [U -> bool]
  reset_fun_tree(&tree);
  set_fun_tree_type(&tree, function_type_desc(&types, tau));

  // add all maps
  for (i=0; i<5; i++) {
    printf("adding map[%"PRIu32"]: ", i);
    fflush(stdout);
    ok = fun_tree_add_map(&tree, map[i]);
    if (ok) {
      printf("OK\n");
    } else {
      printf("Conflict\n");
    }
  }

  // print all the maps;
  printf("\nFinal maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // cleanup
  reset_fun_tree(&tree);
  for (i=0; i<5; i++) {
    free_map(map[i]);
  }

}


/*
 * Like test3 but for maps of type [U -> U]
 */
static void test4(void) {
  particle_t x, y;
  map_t *map[5];
  type_t unint, tau;
  bool ok;
  uint32_t i;

  printf("\n"
         "***********************\n"
	 "*       TEST 4        *\n"
         "***********************\n");

  unint = new_uninterpreted_type(&types);
  x = pstore_labeled_particle(&store, 21, unint);
  y = pstore_labeled_particle(&store, 22, unint);

  // all maps have default false
  map[0] = new_map(1);
  set_map_default(map[0], x);
  normalize_map(map[0]);

  map[1] = new_map(1);
  set_map_default(map[1], y);
  normalize_map(map[1]);

  map[2] = new_map(1);
  set_map_default(map[2], x);
  add_elem_to_map(map[2], x, x);
  normalize_map(map[2]);

  map[3] = new_map(1);
  set_map_default(map[3], y);
  normalize_map(map[3]);

  map[4] = new_map(1);
  set_map_default(map[4], x);
  normalize_map(map[4]);

  // print all the maps;
  printf("\nIinitial maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // prepare the tree
  tau = fun_type1(unint, unint); // [U -> U]
  reset_fun_tree(&tree);
  set_fun_tree_type(&tree, function_type_desc(&types, tau));

  // add all maps
  for (i=0; i<5; i++) {
    printf("adding map[%"PRIu32"]: ", i);
    fflush(stdout);
    ok = fun_tree_add_map(&tree, map[i]);
    if (ok) {
      printf("OK\n");
    } else {
      printf("Conflict\n");
    }
  }

  // print all the maps;
  printf("\nFinal maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // cleanup
  reset_fun_tree(&tree);
  for (i=0; i<5; i++) {
    free_map(map[i]);
  }

}


/*
 * Test5: maps of type [bool -> U]
 */
static void test5(void) {
  particle_t x, y, tt, ff;
  map_t *map[5];
  type_t unint, tau;
  bool ok;
  uint32_t i;

  printf("\n"
         "***********************\n"
	 "*       TEST 5        *\n"
         "***********************\n");

  unint = new_uninterpreted_type(&types);
  x = pstore_labeled_particle(&store, 31, unint);
  y = pstore_labeled_particle(&store, 32, unint);

  tau = bool_type(&types);
  tt = pstore_labeled_particle(&store, 0, tau);
  ff = pstore_labeled_particle(&store, 1, tau);

  map[0] = new_map(1);
  set_map_default(map[0], x);
  normalize_map(map[0]);

  map[1] = new_map(1);
  set_map_default(map[1], y);
  normalize_map(map[1]);

  // fixed map
  map[2] = new_map(1);
  set_map_default(map[2], x);
  add_elem_to_map(map[2], tt, y);
  add_elem_to_map(map[2], ff, x);
  normalize_map(map[2]);

  map[3] = new_map(1);
  set_map_default(map[3], y);
  normalize_map(map[3]);

  // partial map
  map[4] = new_map(1);
  set_map_default(map[4], x);
  add_elem_to_map(map[4], ff, x);
  normalize_map(map[4]);

  // print all the maps;
  printf("\nIinitial maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // prepare the tree
  tau = fun_type1(tau, unint); // [bool -> U]
  reset_fun_tree(&tree);
  set_fun_tree_type(&tree, function_type_desc(&types, tau));

  // add all maps
  for (i=0; i<5; i++) {
    printf("adding map[%"PRIu32"]: ", i);
    fflush(stdout);
    ok = fun_tree_add_map(&tree, map[i]);
    if (ok) {
      printf("OK\n");
    } else {
      printf("Conflict\n");
    }
  }

  // print all the maps;
  printf("\nFinal maps\n");
  for (i=0; i<5; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // cleanup
  reset_fun_tree(&tree);
  for (i=0; i<5; i++) {
    free_map(map[i]);
  }
}


/*
 * Test 6: maps of type [bool, bool -> bool]
 */
static void test6(void) {
  particle_t tt;
  map_t *map[20];
  type_t tau;
  bool ok;
  uint32_t i;

  printf("\n"
         "***********************\n"
	 "*       TEST 6        *\n"
         "***********************\n");

  tau = bool_type(&types);
  tt = pstore_labeled_particle(&store, 0, tau);

  // all maps initially empty, with default value tt
  for (i=0; i<20; i++) {
    map[i] = new_map(1);
    set_map_default(map[i], tt);
    normalize_map(map[i]);
  }

  // print all the maps;
  printf("\nIinitial maps\n");
  for (i=0; i<20; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // prepare the tree
  tau = fun_type2(tau, tau, tau); // [bool, bool -> bool]
  reset_fun_tree(&tree);
  set_fun_tree_type(&tree, function_type_desc(&types, tau));

  // add all maps
  for (i=0; i<20; i++) {
    printf("adding map[%"PRIu32"]: ", i);
    fflush(stdout);
    ok = fun_tree_add_map(&tree, map[i]);
    if (ok) {
      printf("OK\n");
    } else {
      printf("Conflict\n");
    }
  }


  // print all the maps;
  printf("\nFinal maps\n");
  for (i=0; i<20; i++) {
    print_map(map[i]);
  }
  printf("\n");

  // cleanup
  reset_fun_tree(&tree);
  for (i=0; i<20; i++) {
    free_map(map[i]);
  }
}



int main(void) {
  init_type_table(&types, 10);
  init_pstore(&store, &types);
  init_fun_tree(&tree, &store);

  test1();
  test2();
  test3();
  test4();
  test5();
  test6();

  delete_fun_tree(&tree);
  delete_pstore(&store);
  delete_type_table(&types);

  return 0;
}
