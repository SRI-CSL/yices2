/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Substitution context
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "terms/subst_context.h"
#include "utils/int_bv_sets.h"




/*
 * Display the context:
 * format: x<n> := t<m> for the binding n --> m.
 */
static void show_binding(FILE *f, ctx_binding_t *b) {
  fprintf(f, "x%-2"PRId32" := t%"PRId32, b->var, b->term);
}

static void show_context(FILE *f, subst_ctx_t *ctx) {
  int_bvset_t vset;
  uint32_t i;
  int32_t x;

  fputs("active subst:\n", f);
  if (ctx->nelems > 0) {
    i = ctx->nelems;
    init_int_bvset(&vset, 0);
    while (i > 0) {
      i --;
      x = ctx->data[i].var;
      if (int_bvset_add_check(&vset, x)) {
	show_binding(f, ctx->data + i);
	fputc('\n', f);
      }
    }
    delete_int_bvset(&vset);
  }
  fputs("---\n", f);
}


static void show_full_context(FILE *f, subst_ctx_t *ctx) {
  uint32_t i, n;

  fputs("all subst:\n", f);
  n = ctx->nelems;
  for (i=0; i<n; i++) {
    show_binding(f, ctx->data + i);
    fputc('\n', f);
  }
  fputs("---\n", f);
}



/*
 * Test: add mappings for x_1 to x_n
 * x_i is mapped to t_(i+delta)
 */
static void test_add(subst_ctx_t *ctx, int32_t n, int32_t delta) {
  int32_t i, t;

  assert(n >= 0);
  printf("Test: Add mapping:\n");
  for (i=0; i<n; i++) {
    printf("x%-2"PRId32" := t%"PRId32"\n", i, i+delta);
  }
  printf("\n");
  show_context(stdout, ctx);

  for (i=0; i<n; i++) {
    subst_ctx_push_binding(ctx, i, i+delta);
  }
  printf("---> after additions:\n");
  show_context(stdout, ctx);

  printf("---> lookups:\n");
  for (i=0; i<n; i++) {
    t = subst_ctx_lookup(ctx, i);
    printf("lookup(x%"PRId32") = t%"PRId32"\n", i, t);
    if (t != i+delta) {
      printf("ERROR: LOOKUP IS INCORRECT\n");
      fflush(stdout);
      exit(1);
    }
  }

  printf("---> all lookups appear correct\n\n");
}


/*
 * Test: remove last n mappings
 */
static void test_remove(subst_ctx_t *ctx, int32_t n) {
  assert(n >= 0);

  printf("Test: remove last %"PRId32" bindings\n", n);
  show_context(stdout, ctx);
  subst_ctx_pop_bindings(ctx, n);
  printf("---> after removal:\n");
  show_context(stdout, ctx);
  printf("\n");
}


/*
 * Test hash: do it twice
 */
static harray_t *test_hash(subst_ctx_t *ctx) {
  harray_t *a, *b;

  printf("Test hash\n");
  show_context(stdout, ctx);

  a = subst_ctx_hash(ctx);
  printf("hash = %p\n", a);
  b = subst_ctx_hash(ctx);
  if (b != a) {
    printf("ERROR: HASH CONSING INCORRECT\n");
    fflush(stdout);
    exit(1);
  }
  printf("\n");

  return a;
}


/*
 * Store the current mapping of x_0 to x_n-1 into a[0 .. n-1]
 */
static void collect_mapping(subst_ctx_t *ctx, int32_t n, int32_t *a) {
  int32_t i;

  assert(n >= 0);
  for (i=0; i<n; i++) {
    a[i] = subst_ctx_lookup(ctx, i);
  }
}


/*
 * Initialize a[0 ... n-1] to -1 (this means that x_0 to x_{n-1} are unmapped
 */
static void empty_mapping(int32_t n, int32_t *a) {
  int32_t i;

  assert(n >= 0);

  for (i=0; i<n; i++) {
    a[i] = -1;
  }
}


/*
 * Check that the current mapping of x_0 to x_n-1 matches a[0...n-1]
 */
static void check_mapping(subst_ctx_t *ctx, int32_t n, int32_t *a) {
  int32_t i, t;

  assert(n > 0);
  printf("Checking mapping for x%"PRId32" to x%"PRId32"\n", 0, n-1);
  for (i=0; i<n; i++) {
    t = subst_ctx_lookup(ctx, i);
    if (t >= 0) {
      printf("lookup(x%"PRId32") = t%"PRId32"\n", i, t);
    } else {
      printf("lookup(x%"PRId32") = none\n", i);
    }

    if (t != a[i]) {
      printf("ERROR: UNEXPECTED MAPPING FOR x%"PRId32"\n", i);
      fflush(stdout);
      exit(1);
    }
  }
  printf("---> correct mapping\n\n");
}


/*
 * Check that the content of a hashed descriptor d matches a[0 ... n-1]
 */
static void check_hash_content(harray_t *d, int32_t n, int32_t *a) {
  uint32_t i;
  int32_t x, t;

  for (i=0; i<d->nelems; i += 2 ) {
    x = d->data[i];
    t = d->data[i+1];
    if (0 <= x && x < n && a[x] != t) {
      printf("ERROR: INVALID HARRAY CONTENT\n");
      printf(" x%"PRId32" mapped to t%"PRId32" (t%"PRId32" expected)\n", x, t, a[x]);
      fflush(stdout);
      exit(1);
    }
  }
}


/*
 * Global variables:
 * - ctx = the test context
 * - check[NMAPS][NVARS] = arrays to store mapping
 */
#define NMAPS 10
#define NVARS 20

static subst_ctx_t ctx;
static int32_t check[NMAPS][NVARS];

int main(void) {
  harray_t *a1, *a2, *a3, *a4;
  harray_t *tmp;

  init_subst_ctx(&ctx, 4);

  printf("Initial context\n");
  show_context(stdout, &ctx);

  empty_mapping(NVARS, check[0]);
  check_mapping(&ctx, NVARS, check[0]);
  a1 = test_hash(&ctx);
  check_hash_content(a1, NVARS, check[0]);

  test_add(&ctx, 5, 100);
  collect_mapping(&ctx, NVARS, check[1]);
  a2 = test_hash(&ctx);
  check_hash_content(a2, NVARS, check[1]);

  test_add(&ctx, 10, 200);
  collect_mapping(&ctx, NVARS, check[2]);
  a3 = test_hash(&ctx);
  check_hash_content(a3, NVARS, check[2]);

  test_add(&ctx, 8, 300);
  collect_mapping(&ctx, NVARS, check[3]);
  a4 = test_hash(&ctx);
  check_hash_content(a4, NVARS, check[3]);

  printf("\n\nFull content after additions\n");
  show_full_context(stdout, &ctx);
  printf("\n\n");

  printf("\n\nReset:\n");
  reset_subst_ctx(&ctx, false);
  show_context(stdout, &ctx);
  printf("\n\n");


  /*
   * Re-add the bindings as before the reset.
   * - the hash codes a1, a2, a3, a4
   *   should still be valid
   */
  check_mapping(&ctx, NVARS, check[0]);
  tmp = test_hash(&ctx);
  check_hash_content(tmp, NVARS, check[0]);
  if (tmp != a1) {
    printf("ERROR: HASH-CONSING FAILED\n");
    fflush(stdout);
    exit(1);
  }

  test_add(&ctx, 5, 100);
  check_mapping(&ctx, NVARS, check[1]);
  tmp = test_hash(&ctx);
  check_hash_content(tmp, NVARS, check[1]);
  if (tmp != a2) {
    printf("ERROR: HASH-CONSING FAILED\n");
    fflush(stdout);
    exit(1);
  }

  test_add(&ctx, 10, 200);
  check_mapping(&ctx, NVARS, check[2]);
  tmp = test_hash(&ctx);
  check_hash_content(tmp, NVARS, check[2]);
  if (tmp != a3) {
    printf("ERROR: HASH-CONSING FAILED\n");
    fflush(stdout);
    exit(1);
  }

  test_add(&ctx, 8, 300);
  check_mapping(&ctx, NVARS, check[3]);
  tmp = test_hash(&ctx);
  check_hash_content(tmp, NVARS, check[3]);
  if (tmp != a4) {
    printf("ERROR: HASH-CONSING FAILED\n");
    fflush(stdout);
    exit(1);
  }

  /*
   * Remove the bindings in reverse order
   */
  test_remove(&ctx, 8);
  check_mapping(&ctx, NVARS, check[2]);
  tmp = test_hash(&ctx);
  if (tmp != a3) {
    printf("ERROR: HASH-CONSING FAILED\n");
    fflush(stdout);
    exit(1);
  }

  test_remove(&ctx, 10);
  check_mapping(&ctx, NVARS, check[1]);
  tmp = test_hash(&ctx);
  if (tmp != a2) {
    printf("ERROR: HASH-CONSING FAILED\n");
    fflush(stdout);
    exit(1);
  }

  test_remove(&ctx, 5);
  check_mapping(&ctx, NVARS, check[0]);
  tmp = test_hash(&ctx);
  if (tmp != a1) {
    printf("ERROR: HASH-CONSING FAILED\n");
    fflush(stdout);
    exit(1);
  }


  delete_subst_ctx(&ctx);

  return 0;
}
