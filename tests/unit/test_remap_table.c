/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the substitution/remap table for pseudo literals
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/bv/remap_table.h"
#include "utils/memalloc.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Print pseudo literal l: as s!i or ~s!i
 */
static void print_pseudo_literal(FILE *f, literal_t l) {
  assert(l != null_literal);
  if (l == true_literal) {
    fputs(" ttt   ", f);
  } else if (l == false_literal) {
    fputs(" fff   ", f);
  } else {
    if (is_neg(l)) {
      fputc('~', f);
    } else {
      fputc(' ', f);
    }
    fprintf(f, "s!%-4"PRId32, var_of(l));
  }
}


/*
 * Print literal l as p!i or ~p!i
 */
static void print_literal(FILE *f, literal_t l) {
  if (l == null_literal) {
    fputs(" nil   ", f);
  } else if (l == true_literal) {
    fputs(" tt    ", f);
  } else if (l == false_literal) {
    fputs(" ff    ", f);
  } else {
    if (is_neg(l)) {
      fputc('~', f);
    } else {
      fputc(' ', f);
    }
    fprintf(f, "p!%-4"PRId32, var_of(l));
  }
}


/*
 * Display the content of a remap table
 */
static void show_full_remap(remap_table_t *table) {
  uint32_t n;
  literal_t s, r, l;

  n = 2 * table->nvars;
  for (s=0; s<n; s++) {
    r = remap_table_find_root(table, s);
    l = remap_table_find(table, s);

    print_pseudo_literal(stdout, s);
    printf(": root = ");
    print_pseudo_literal(stdout, r);
    printf(", map = ");
    print_literal(stdout, l);
    printf("\n");
  }
}


// skip the non-mapped literals
static void show_remap(remap_table_t *table) {
  uint32_t n;
  literal_t s, r, l;

  n = 2 * table->nvars;
  for (s=0; s<n; s++) {
    r = remap_table_find_root(table, s);
    l = remap_table_find(table, s);

    if (r != s || l != null_literal) {
      print_pseudo_literal(stdout, s);
      printf(": root = ");
      print_pseudo_literal(stdout, r);
      printf(", map = ");
      print_literal(stdout, l);
      printf("\n");
    }
  }
}


/*
 * Structure to store the full content of a remap table
 * - nlits = number of literals
 * - root[l] = root of literal l
 * - map[l] = real literal mapped to l
 */
typedef struct remap_content_s {
  uint32_t nlits;
  literal_t *root;
  literal_t *map;
} remap_content_t;



/*
 * Copy the content of table into s
 */
static void extract_remap(remap_table_t *table, remap_content_t *s) {
  uint32_t n;
  literal_t l;

  n = 2 * table->nvars;
  s->nlits = n;
  s->root = (literal_t *) safe_malloc(n * sizeof(literal_t));
  s->map = (literal_t *) safe_malloc(n * sizeof(literal_t));

  for (l=0; l<n; l++) {
    s->root[l] = remap_table_find_root(table, l);
    s->map[l] = remap_table_find(table, l);
  }
}


/*
 * Check whether table has the same content as s
 */
static bool check_remap_content(remap_table_t *table, remap_content_t *s) {
  uint32_t n;
  literal_t l;

  n = 2 * table->nvars;
  if (s->nlits != n) {
    return false;
  }

  for (l=0; l<n; l++) {
    if (s->root[l] != remap_table_find_root(table, l) ||
	s->map[l] != remap_table_find(table, l)) {
      return false;
    }
  }

  return true;
}



/*
 * Delete record s
 */
static void delete_content(remap_content_t *s) {
  safe_free(s->root);
  safe_free(s->map);
  s->root = NULL;
  s->map = NULL;
}



/*
 * Pick a random literal from array v
 * - n = size of the array
 */
static literal_t sample_literal(literal_t *v, uint32_t n) {
  uint32_t i;
  literal_t l;

  i = random() % n;
  l = v[i];
  if (random() & 0x8000) {
    l = not(l);
  }
  return l;
}



/*
 * Test merging of l1 and l2
 */
static void test_merge(remap_table_t *table, literal_t l1, literal_t l2) {
  literal_t r1, r2;

  printf("test_merge: ");
  print_pseudo_literal(stdout, l1);
  printf(" and ");
  print_pseudo_literal(stdout, l2);
  printf("\n");

  if (remap_table_mergeable(table, l1, l2)) {
    remap_table_merge(table, l1, l2);
    r1 = remap_table_find_root(table, l1);
    r2 = remap_table_find_root(table, l2);
    printf("after merge: root of ");
    print_pseudo_literal(stdout, l1);
    printf(" = ");
    print_pseudo_literal(stdout, r1);
    printf(" and root of ");
    print_pseudo_literal(stdout, l2);
    printf(" = ");
    print_pseudo_literal(stdout, r2);
    printf("\n\n");
    fflush(stdout);

    assert(r1 == r2 && (r1 == l1 || r2 == l2));

  } else {
    printf("not mergeable\n\n");
  }
}




/*
 * Select randomly k pairs of literals from v then
 * try to merge them.
 * - n = size of v
 */
static void random_merges(remap_table_t *table, literal_t *v, uint32_t n, uint32_t k) {
  literal_t l1, l2;

  while (k > 0) {
    k --;
    l1 = sample_literal(v, n);
    if (! remap_table_is_root(table, l1)) {
      l1 = remap_table_find_root(table, l1);
    }

    l2 = sample_literal(v, n);
    if (! remap_table_is_root(table, l2)) {
      l2 = remap_table_find_root(table, l2);
    }

    test_merge(table, l1, l2);
  }
}



/*
 * Test assigning l to s
 */
static void test_remap(remap_table_t *table, literal_t s, literal_t l) {
  literal_t l0;

  printf("test_remap: ");
  print_pseudo_literal(stdout, s);
  printf(" to ");
  print_literal(stdout, l);
  printf("\n");

  l0 = remap_table_find(table, s);
  if (l0 != null_literal) {
    printf("failed: ");
    print_pseudo_literal(stdout, s);
    printf(" already mapped to ");
    print_literal(stdout, l0);
    printf("\n\n");
  } else {
    remap_table_assign(table, s, l);
    printf("done: ");
    l0 = remap_table_find(table, s);
    print_pseudo_literal(stdout, s);
    printf(" now mapped to ");
    print_literal(stdout, l0);
    printf("\n\n");

    assert(l0 == l);
  }
}


/*
 * Select randomly k literals from v and test remap for them
 * - n = size of v
 */
static void random_remaps(remap_table_t *table, literal_t *v, uint32_t n, uint32_t k) {
  literal_t s, l;

  while (k > 0) {
    k --;
    s = sample_literal(v, n);
    l = random() & 0xff;
    test_remap(table, s, l);
  }
}




static remap_table_t map;
static remap_content_t save[5];

int main(void) {
  literal_t *v, *w;

  init_remap_table(&map);

  printf("--- Initial table ---\n");
  show_full_remap(&map);
  printf("----\n");

  reset_remap_table(&map);
  printf("--- After reset ---\n");
  show_full_remap(&map);
  printf("----\n");

  v = remap_table_fresh_array(&map, 100);
  int_array_incref(v);

  printf("--- After allocating 100 pseudo literals ---\n");
  show_full_remap(&map);
  printf("----\n");

  printf("--- Level 0 ---\n");
  random_merges(&map, v, 100, 20);
  printf("--- After 20 random merges ---\n");
  show_remap(&map);
  printf("----\n");
  random_remaps(&map, v, 100, 20);
  printf("--- After 20 random remaps ---\n");
  show_remap(&map);
  printf("----\n");
  extract_remap(&map, save + 0);

  remap_table_push(&map);

  printf("--- Level 1 ---\n");
  random_merges(&map, v, 100, 20);
  printf("--- After 20 random merges ---\n");
  show_remap(&map);
  printf("----\n");
  random_remaps(&map, v, 100, 20);
  printf("--- After 20 random remaps ---\n");
  show_remap(&map);
  printf("----\n");
  extract_remap(&map, save + 1);

  remap_table_push(&map);

  printf("--- Level 2: allocating 40 more literals ---\n");
  w  = remap_table_fresh_array(&map, 40);
  int_array_incref(w);

  random_merges(&map, w, 40, 10);
  random_merges(&map, v, 100, 10);
  printf("--- After 20 random merges ---\n");
  show_remap(&map);
  printf("----\n");
  random_remaps(&map, v, 100, 20);
  random_remaps(&map, w, 40, 20);
  printf("--- After 40 random remaps ---\n");
  show_remap(&map);
  printf("----\n");
  extract_remap(&map, save + 2);

  remap_table_push(&map);

  printf("--- Level 3 ---\n");
  random_merges(&map, w, 40, 20);
  random_merges(&map, v, 100, 10);
  printf("--- After 20 random merges ---\n");
  show_remap(&map);
  printf("----\n");
  random_remaps(&map, v, 100, 20);
  random_remaps(&map, w, 40, 20);
  printf("--- After 40 random remaps ---\n");
  show_remap(&map);
  printf("----\n");

  remap_table_pop(&map);
  printf("--- Back to level 2 ---\n");
  show_remap(&map);
  printf("----\n");
  if (! check_remap_content(&map, save + 2)) {
    printf("*** BUG: Pop error ***\n");
    abort();
  }

  remap_table_free_array(w);

  remap_table_pop(&map);
  printf("--- Back to level 1 ---\n");
  show_remap(&map);
  printf("----\n");
  if (! check_remap_content(&map, save + 1)) {
    printf("*** BUG: Pop error ***\n");
    abort();
  }

  remap_table_pop(&map);
  printf("--- Back to level 0 ---\n");
  show_remap(&map);
  printf("----\n");
  if (! check_remap_content(&map, save + 0)) {
    printf("*** BUG: Pop error ***\n");
    abort();
  }

  delete_content(save + 0);
  delete_content(save + 1);
  delete_content(save + 2);

  remap_table_free_array(v);

  delete_remap_table(&map);

  return 0;
}
