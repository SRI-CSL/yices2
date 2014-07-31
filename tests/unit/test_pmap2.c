/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST OF MAPPING (int, int -> int)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/pair_hash_map2.h"


/*
 * Print a map element
 */
static void print_map_record(FILE *f, pmap2_rec_t *e) {
  fprintf(f, "<%"PRId32", %"PRId32"> --> %"PRId32"\n", e->k0, e->k1, e->val);
}

/*
 * Print the full map
 */
static void print_map(FILE *f, pmap2_t *map) {
  pmap2_htbl_t *htbl;
  pmap2_rec_t *e;
  uint32_t i, n;

  htbl = &map->htbl;
  fprintf(f, "map: %"PRIu32" records, %"PRIu32" deletions, size = %"PRIu32"\n",
	  htbl->nelems, htbl->ndeleted, htbl->size);

  n = htbl->size;
  for (i=0; i<n; i++) {
    e = htbl->data[i];
    if (e != NULL && e != PMAP2_DELETED) {
      fprintf(f, "    %4"PRIu32": ", i);
      print_map_record(f, e);
    }
  }
  fprintf(f, "\n");
}


/*
 * Print the push/pop stack
 */
static void print_stack(FILE *f, pmap2_t *map) {
  pmap2_stack_t *stack;
  uint32_t i, n;

  stack = &map->stack;

  fprintf(f, "stack:\n");
  fprintf(f, "  size = %"PRIu32"\n", stack->size);
  fprintf(f, "  current_level = %"PRIu32"\n", stack->current_level);
  fprintf(f, "  top_level = %"PRIu32"\n", stack->top_level);

  n = stack->nmarks;
  if (n == 0) {
    fprintf(f, "  no alloc marks\n");
  } else {
    for (i=0; i<n; i++) {
      fprintf(f, "  mark[%"PRIu32"]: level = %"PRIu32", block = %"PRIu32", index = %"PRIu32"\n",
	      i, stack->data[i].level, stack->data[i].block_id, stack->data[i].alloc_idx);
    }
  }
  fprintf(f, "\n");
}


/*
 * Print bank
 */
static void print_bank(FILE *f, pmap2_t *map) {
  pmap2_bank_t *bank;
  uint32_t i, n;

  bank = &map->bank;
  fprintf(f, "bank:\n");
  fprintf(f, "  capacity = %"PRIu32"\n", bank->capacity);
  fprintf(f, "  nblocks = %"PRIu32"\n", bank->nblocks);
  fprintf(f, "  free_block = %"PRIu32"\n", bank->free_block);
  fprintf(f, "  alloc_ptr = %"PRIu32"\n", bank->alloc_ptr);

  n = bank->nblocks;
  for (i=0; i<n; i++) {
    fprintf(f, "  block[%"PRIu32"] = %p\n", i, bank->block[i]);
  }
}



/*
 * Global map for testing
 */
static pmap2_t map;


/*
 * Test: find/get element with key <k0, k1>
 */
static void test_elem(int32_t k0, int32_t k1) {
  pmap2_rec_t *e, *e0;

  printf("\n--- Testing key = <%"PRId32", %"PRId32"> ---\n", k0, k1);

  e0 = pmap2_find(&map, k0, k1);
  if (e0 == NULL) {
    printf("find: returned NULL\n");
  } else {
    printf("find: returned %p: ", e0);
    print_map_record(stdout, e0);
    printf("\n");
  }

  e = pmap2_get(&map, k0, k1);
  printf("get: returned %p: ", e);
  print_map_record(stdout, e);

  if (e0 == NULL) {
    if (e->val != -1) {
      printf("*** BUG: inconsitency between find and get ***\n");
    } else {
      printf("new record: setting value to %"PRId32"\n", k0 + k1);
      e->val = k0 + k1;
    }
  } else if (e != e0) {
    printf("*** BUG in hash table ***\n");
  }


  e0 = pmap2_find(&map, k0, k1);
  if (e0 == NULL) {
    printf("find: returned NULL\n");
  } else {
    printf("find: returned %p: ", e0);
    print_map_record(stdout, e0);
    printf("\n");
  }

  if (e != e0) {
    printf("*** BUG in hash table ***\n");
  }
}



static void test1(void) {
  int32_t i, j;

  printf("************\n"
	 "*  TEST 1  *\n"
	 "************\n");

  init_pmap2(&map);
  printf("\n--- Initial map ---\n");
  print_map(stdout, &map);

  for (i=0; i<10; i++) {
    printf("\n--- Push ---\n");
    pmap2_push(&map);
    print_stack(stdout, &map);

    printf("\n--- Row %"PRId32" ---\n", i);
    for (j=0; j<10; j++) {
      test_elem(i, j);
    }
    print_map(stdout, &map);

    printf("\n--- Push ---\n");
    pmap2_push(&map);
    print_stack(stdout, &map);
  }

  printf("\n--- Final map ---\n");
  print_map(stdout, &map);
  print_stack(stdout, &map);
  print_bank(stdout, &map);

  reset_pmap2(&map);
  printf("\n--- After reset ---\n");
  print_map(stdout, &map);
  print_stack(stdout, &map);
  print_bank(stdout, &map);

  for (i=0; i<50; i++) {
    printf("\n--- Push ---\n");
    pmap2_push(&map);
    print_stack(stdout, &map);

    printf("\n--- Row %"PRId32" ---\n", i);
    for (j=0; j<50; j++) {
      test_elem(i, j);
    }
    print_map(stdout, &map);

    printf("\n--- Push ---\n");
    pmap2_push(&map);
    print_stack(stdout, &map);
  }

  printf("\n--- Final map ---\n");
  print_map(stdout, &map);
  print_stack(stdout, &map);
  print_bank(stdout, &map);


  i = map.stack.current_level;
  while (i > 20) {
    printf("\n--- Pop ---\n");
    pmap2_pop(&map);
    print_map(stdout, &map);
    print_stack(stdout, &map);
    print_bank(stdout, &map);
    i --;
  }

  for (i=0; i<50; i++) {
    printf("\n--- Row %"PRId32" ---\n", i);
    for (j=0; j<50; j++) {
      test_elem(i, j);
    }
    print_map(stdout, &map);

    if (i % 4 == 0) {
      printf("\n--- Push ---\n");
      pmap2_push(&map);
      print_stack(stdout, &map);
    }
  }


  i = map.stack.current_level;
  while (i > 0) {
    printf("\n--- Pop ---\n");
    pmap2_pop(&map);
    print_map(stdout, &map);
    print_stack(stdout, &map);
    print_bank(stdout, &map);
    i --;
  }


  delete_pmap2(&map);
}



int main(void) {
  test1();
  return 0;
}
