/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the basic cache
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/cache.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif



/*
 * Tags for testing
 */
enum {
  A, B, C, D,
} test_tag;

#define NUMTAGS (D+1)

static const char * const tag2string[NUMTAGS] = {
  "A", "B", "C", "D",
};


/*
 * Print a cache element
 */
static void print_cache_elem(FILE *f, cache_elem_t *e) {
  assert(e->tag < NUMTAGS);
  fprintf(f, "[%s %2"PRId32" %2"PRId32"]   (flag = %2"PRIu16")",
	  tag2string[e->tag], e->data[0], e->data[1], e->flag);
}

/*
 * Print the full content of a cache
 */
static void print_all_cache(FILE *f, cache_t *cache) {
  cache_htbl_t *htbl;
  uint32_t i, n;
  cache_elem_t *e;

  htbl = &cache->htbl;
  fprintf(f, "Cache: %"PRIu32" elements, size = %"PRIu32"\n",
	  htbl->nelems, htbl->size);
  n = htbl->size;
  for (i=0; i<n; i++) {
    e = htbl->data[i];
    if (e != NULL && e != DELETED_ELEM) {
      fprintf(f, "   %4"PRIu32": ", i);
      print_cache_elem(f, e);
      fprintf(f, "\t hash MOD size = %"PRIu32"\n", (e->hash % htbl->size));
    }
  }
  fprintf(f, "\n");
}


/*
 * Print push/pop stack
 */
static void print_cache_stack(FILE *f, cache_t *cache) {
  cache_levstack_t *stack;
  uint32_t i, n;

  stack = &cache->stack;

  fprintf(f, "push/pop stack:\n");
  fprintf(f, "  size = %"PRIu32"\n", stack->size);
  fprintf(f, "  current_level = %"PRIu32"\n", stack->current_level);
  fprintf(f, "  top_level = %"PRIu32"\n", stack->top_level);
  n = stack->nmarks;
  if (n == 0) {
    fprintf(f, "  no marks\n");
  } else {
    for (i=0; i<n; i++) {
      fprintf(f, "  mark[%"PRIu32"]: level = %"PRIu32", blk_id = %"PRIu32", index = %"PRIu32"\n",
	      i, stack->data[i].level, stack->data[i].blk_id, stack->data[i].index);
    }
  }
}


/*
 * Print bank
 */
static void print_cache_bank(FILE *f, cache_t *cache) {
  cache_bank_t *bnk;
  uint32_t i, n;

  bnk = &cache->bank;
  fprintf(f, "bank:\n");
  fprintf(f, "  capacity = %"PRIu32"\n", bnk->capacity);
  fprintf(f, "  nblocks = %"PRIu32"\n", bnk->nblocks);
  fprintf(f, "  free_block = %"PRIu32"\n", bnk->free_block);
  fprintf(f, "  alloc_ptr = %"PRIu32"\n", bnk->alloc_ptr);
  n = bnk->nblocks;
  for (i=0; i<n; i++) {
    fprintf(f, "  block[%"PRIu32"] = %p\n", i, bnk->block[i]);
  }
}



/*
 * Global cache
 */
static cache_t cache;


/*
 * Test: add an element
 */
static void test_elem(uint16_t tag, int32_t x, int32_t y) {
  cache_elem_t *e, *e0;

  assert(tag < NUMTAGS);
  printf("\n--- Testing element [%s %"PRId32" %"PRId32"] ---\n", tag2string[tag], x, y);

  // find 1
  e0 = cache_find(&cache, tag, x, y);
  if (e0 == NULL) {
    printf("find: returned NULL\n");
  } else {
    printf("find: returned %p: ", e0);
    print_cache_elem(stdout, e0);
    printf("\n");
  }

  // get
  e = cache_get(&cache, tag, x, y);
  assert(e != NULL);
  printf("get:  returned %p: ", e);
  print_cache_elem(stdout, e);
  printf("\n");
  if (e0 == NULL) {
    if (e->flag != NEW_CACHE_ELEM) {
      printf("*** inconsistency between find and get ***\n");
    } else {
      printf("new element: setting flag to 17\n");
      e->flag = 17;
    }
  } else if (e != e0) {
    printf("*** caching bug ***\n");
  }

  // find 2
  e0 = cache_find(&cache, tag, x, y);
  if (e0 == NULL) {
    printf("find: returned NULL\n");
  } else {
    printf("find: returned %p: ", e0);
    print_cache_elem(stdout, e0);
    printf("\n");
  }
  if (e != e0) {
    printf("*** inconsistency between find and get ***\n");
  }
}


static void test1(void) {
  printf("***************************\n"
	 "*        TEST 1           *\n"
	 "***************************\n");

  init_cache(&cache);
  printf("\n--- Initial cache ---\n");
  print_all_cache(stdout, &cache);

  test_elem(A, 1, 1);
  test_elem(A, 1, 1);

  printf("\n--- After addition ---\n");
  print_all_cache(stdout, &cache);

  test_elem(B, 2, 2);
  test_elem(B, 2, 2);

  printf("\n--- After more addition ---\n");
  print_all_cache(stdout, &cache);

  cache_push(&cache);
  cache_push(&cache);
  printf("\n--- Push: level 2 ---\n");
  print_all_cache(stdout, &cache);

  test_elem(A, 0, 1);
  test_elem(A, 0, 1);

  test_elem(A, 1, 0);
  test_elem(A, 1, 0);

  printf("\n--- Content ---\n");
  print_all_cache(stdout, &cache);

  cache_push(&cache);
  printf("\n--- Push: level 3 ---\n");
  print_all_cache(stdout, &cache);

  cache_pop(&cache);
  printf("\n--- Pop: level 2 ---\n");
  print_all_cache(stdout, &cache);

  cache_pop(&cache);
  printf("\n--- Pop: level 1 ---\n");
  print_all_cache(stdout, &cache);

  cache_pop(&cache);
  printf("\n--- Pop: level 0 ---\n");
  print_all_cache(stdout, &cache);

  delete_cache(&cache);
}


static void test2(void) {
  uint16_t tag;
  int32_t x, y;
  uint32_t i;
  cache_elem_t *e0, *e1;
  uint32_t level;


  printf("***************************\n"
	 "*        TEST 2           *\n"
	 "***************************\n");

  level = 1;

  init_cache(&cache);
  printf("---- INITIAL ----\n");
  print_cache_stack(stdout, &cache);
  print_cache_bank(stdout, &cache);
  printf("\n");

  for (i=0; i<4000; i++) {
    tag = (uint16_t) (random() % NUMTAGS);
    x = (int32_t) (random() % 20);
    y = (int32_t) (random() % 20);
    e0 = cache_find(&cache, tag, x, y);
    e1 = cache_get(&cache, tag, x, y);

    if (e0 == NULL && e1->flag != NEW_CACHE_ELEM) {
      printf("*** caching bug ***\n");
      printf("  element: [%s %"PRId32" %"PRId32"]\n", tag2string[tag], x, y);
      printf("  find: returned NULL\n");
      printf("  get:  returned %p: ", e1);
      print_cache_elem(stdout, e1);
      printf("\n");
    }

    if (e0 != NULL && e1 != e0) {
      printf("*** caching bug ***\n");
      printf("  element: [%s %"PRId32" %"PRId32"]\n", tag2string[tag], x, y);
      printf("  find: returned %p: ", e0);
      print_cache_elem(stdout, e0);
      printf("\n");
      printf("  get:  returned %p: ", e1);
      print_cache_elem(stdout, e1);
      printf("\n");
    }

    if (e1->flag == NEW_CACHE_ELEM) {
      e1->flag = (uint16_t) level;
    }

    if (i % 100 == 49) {
      printf("\n--- Push to level %"PRIu32" ---\n", level);
      cache_push(&cache);
      level ++;
      print_cache_stack(stdout, &cache);
      print_cache_bank(stdout, &cache);
    }
  }

  printf("\n--- After random additions (level = %"PRIu32") ---\n", level);
  print_all_cache(stdout, &cache);
  print_cache_stack(stdout, &cache);
  print_cache_bank(stdout, &cache);

  while (level > 1) {
    level --;
    printf("\n--- Pop to level %"PRIu32" ---\n", level);
    cache_pop(&cache);
    print_all_cache(stdout, &cache);
    print_cache_stack(stdout, &cache);
    print_cache_bank(stdout, &cache);
  }

  printf("\n--- After reset ---\n");
  reset_cache(&cache);
  print_all_cache(stdout, &cache);
  print_cache_stack(stdout, &cache);
  print_cache_bank(stdout, &cache);

  delete_cache(&cache);
}

int main(void) {
  test1();
  test2();
  return 0;
}
