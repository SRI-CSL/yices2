/*
 * Regression tests for type-table garbage collection.
 *
 * - A deleted type leaves a hole in the table that the next collection
 *   scans; reading its GC mark used to trip the good_type assertion.
 * - The GC filter for the max-supertype cache was inverted: it dropped
 *   the live records and kept the stale ones, so a new type that reused a
 *   deleted type's id got that type's cached (deleted) max supertype.
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "api/yices_globals.h"
#include "terms/types.h"
#include "yices.h"

static void check(bool cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "type_table_gc: %s\n", msg);
    fflush(stderr);
    exit(2);
  }
}

static void test_gc_with_deleted_types(void) {
  type_t bv;

  bv = yices_bv_type(17);
  check(bv != NULL_TYPE, "yices_bv_type failed");

  // nothing references bv: the first GC deletes it, the second scans the hole
  yices_garbage_collect(NULL, 0, NULL, 0, false);
  check(bad_type(__yices_globals.types, bv), "unreferenced type survived the GC");
  yices_garbage_collect(NULL, 0, NULL, 0, false);
}

static void test_max_cache_after_gc(void) {
  type_table_t *types = __yices_globals.types;
  type_t int_type, real_type, bool_type;
  type_t max, tau, sigma, sigma_max;

  int_type = yices_int_type();
  real_type = yices_real_type();
  bool_type = yices_bool_type();

  // create max before tau so that tau's id is the first one reused after GC
  max = yices_function_type1(int_type, real_type);
  tau = yices_function_type1(int_type, int_type);
  check(max_super_type(types, tau) == max, "wrong max supertype for [int -> int]");

  yices_garbage_collect(NULL, 0, NULL, 0, false);
  check(bad_type(types, tau) && bad_type(types, max), "unreferenced types survived the GC");

  sigma = yices_function_type1(bool_type, int_type);
  if (sigma != tau) {
    fprintf(stderr, "type_table_gc: type id not reused, skipping max-cache check\n");
    return;
  }

  // query before creating [bool -> real], which would take max's old id
  sigma_max = max_super_type(types, sigma);
  check(good_type(types, sigma_max), "max supertype of [bool -> int] is a deleted type");
  check(sigma_max == yices_function_type1(bool_type, real_type),
        "wrong max supertype for [bool -> int]");
}

int main(void) {
  yices_init();

  test_gc_with_deleted_types();
  test_max_cache_after_gc();

  yices_exit();

  return 0;
}
