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

/*
 * TEST FUNCTIONS TO SET THE SEARCH PARAMETERS
 */

#include <assert.h>
#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdlib.h>

#include "api/search_parameters.h"
#include "yices.h"


/*
 * Convert boolean b to a string
 */
static const char *bool2string(bool x) {
  return x ? "true" : "false";
}


/*
 * Convert branching code c to a string
 */
static const char *const branching2string[NUM_BRANCHING_MODES] = {
  "default",
  "negative",
  "positive",
  "theory",
  "th-neg",
  "th-pos",
};


/*
 * Print a configuration descriptor
 */
static void show_params(param_t *params) {
  printf("param record: %p\n", params);
  printf("--- restart ---\n");
  printf("  fast-restart = %s\n", bool2string(params->fast_restart));
  printf("  c-threshold  = %"PRIu32"\n", params->c_threshold);
  printf("  d-threshold  = %"PRIu32"\n", params->d_threshold);
  printf("  c-factor     = %.4f\n", params->c_factor);
  printf("  d-factor     = %.4f\n", params->d_factor);
  printf("--- clause deletion ---\n");
  printf("  r-initial-threshold  = %"PRIu32"\n", params->r_initial_threshold);
  printf("  r-interval           = %"PRIu32"\n", params->r_interval);
  printf("--- core ---\n");
  printf("  var-decay     = %.4f\n", params->var_decay);
  printf("  randomness    = %.4f\n", (double) params->randomness);
  printf("  random_seed   = %"PRIu32"\n", params->random_seed);
  printf("  branching     = %s\n", branching2string[params->branching]);
  printf("  clause-decay  = %.4f\n", (double) params->clause_decay);
  printf("  cache-tclause = %s\n", bool2string(params->cache_tclauses));
  printf("  tclause-size  = %"PRIu32"\n", params->tclause_size);
  printf("--- egraph ---\n");
  printf("  use_dyn_ack            = %s\n", bool2string(params->use_dyn_ack));
  printf("  use_bool_dyn_ack       = %s\n", bool2string(params->use_bool_dyn_ack));
  printf("  max_ackermann          = %"PRIu32"\n", params->max_ackermann);
  printf("  max_boolackermann      = %"PRIu32"\n", params->max_boolackermann);
  printf("  aux_eq_quota           = %"PRIu32"\n", params->aux_eq_quota);
  printf("  aux_eq_ratio           = %.4f\n", params->aux_eq_ratio);
  printf("  dyn_ack_threshold      = %"PRIu32"\n", (uint32_t) params->dyn_ack_threshold);
  printf("  dyn_bool_ack_threshold = %"PRIu32"\n", (uint32_t) params->dyn_bool_ack_threshold);
  printf("  max_interface_eqs      = %"PRIu32"\n", params->max_interface_eqs);
  printf("--- simplex ---\n");
  printf("  use_simplex_prop       = %s\n", bool2string(params->use_simplex_prop));
  printf("  adjust_simplex_model   = %s\n", bool2string(params->adjust_simplex_model));
  printf("  integer_check          = %s\n", bool2string(params->integer_check));
  printf("  max_prop_row_size      = %"PRIu32"\n", params->max_prop_row_size);
  printf("  bland_threshold        = %"PRIu32"\n", params->bland_threshold);
  printf("  integer_check_period   = %"PRIu32"\n", params->integer_check_period);
  printf("--- array solver ---\n");
  printf("  max_update_conflicts   = %"PRIu32"\n", params->max_update_conflicts);
  printf("  max_extensionality     = %"PRIu32"\n", params->max_extensionality);
  printf("\n");
  fflush(stdout);
}



/*
 * Test of set_param:
 * - name = test parameter name
 * - value = test value
 * - k = expected returned value
 * - error = expected error code (if k < 0)
 */
static void test_set_param(param_t *params, const char *name, const char *value, int32_t k, int32_t error) {
  int32_t code;
  error_code_t ecode;

  printf("Testing set_param %s := %s: ", name, value);
  fflush(stdout);
  code = yices_set_param(params, name, value);
  if (code >= 0) {
    printf("ok\n");
    show_params(params);
  } else {
    printf("error\n");
    yices_print_error(stdout);
  }

  if (code != k) {
    printf("TEST FAILED\n");
    printf("--> Yices function returned %"PRId32"; %"PRId32" was expected\n", code, k);
    fflush(stdout);
    exit(1);
  } else if (k < 0) {
    ecode = yices_error_code();
    if (ecode != error) {
      printf("TEST FAILED\n");
      printf("--> Found error code %"PRId32"; %"PRId32" was expected\n", ecode, error);
      fflush(stdout);
      exit(1);
    }
  }

  printf("\n");
  fflush(stdout);
}


/*
 * Boolean parameter
 */
static void test_set_bool_param(param_t *params, const char *name) {
  test_set_param(params, name, "true", 0, 0);
  test_set_param(params, name, "false", 0, 0);
  test_set_param(params, name, "TRUE", 0, 0);
  test_set_param(params, name, "FALSE", 0, 0);
  test_set_param(params, name, "maybe", -1, CTX_INVALID_PARAMETER_VALUE);
}

/*
 * Integer parameter in the interval [1 .. INT32_MAX]
 */
static void test_set_posint_param(param_t *params, const char *name) {
  test_set_param(params, name, "1", 0, 0);
  test_set_param(params, name, "1000", 0, 0);
  test_set_param(params, name, "2147483647", 0, 0);

  test_set_param(params, name, "0", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "-100", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "2147483648", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_param(params, name, "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);
}


/*
 * Integer parameter in the interval [2, INT32_MAX]
 */
static void test_set_posint2_param(param_t *params, const char *name) {
  test_set_param(params, name, "2", 0, 0);
  test_set_param(params, name, "1000", 0, 0);
  test_set_param(params, name, "2147483647", 0, 0);

  test_set_param(params, name, "1", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "-100", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "2147483648", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_param(params, name, "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);
}


/*
 * Integer parameter in the interval 01 .. INT32_MAX]
 */
static void test_set_nonnegint_param(param_t *params, const char *name) {
  test_set_param(params, name, "0", 0, 0);
  test_set_param(params, name, "1000", 0, 0);
  test_set_param(params, name, "2147483647", 0, 0);

  test_set_param(params, name, "-1", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "-100", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "2147483648", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_param(params, name, "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);
}


/*
 * Integer parameter in the interval [1, UINT16_MAX]
 */
static void test_set_posint16_param(param_t *params, const char *name) {
  test_set_param(params, name, "1", 0, 0);
  test_set_param(params, name, "1000", 0, 0);
  test_set_param(params, name, "65535", 0, 0);

  test_set_param(params, name, "0", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "-100", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "65536", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_param(params, name, "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);
}


/*
 * Unsigned integer paramer (32bits)
 */
static void test_set_uint32_pram(param_t *params, const char *name) {
  test_set_param(params, name, "0", 0, 0);
  test_set_param(params, name, "111111111", 0, 0);
  test_set_param(params, name, "4294967295", 0, 0); // 2^32 - 1
  test_set_param(params, name, "0xabcdef98", 0, 0); // hexadecimal format is allowed
  test_set_param(params, name, "0777777777", 0, 0); // octal format is allowed

  test_set_param(params, name, "-10", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "4294967296", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_param(params, name, "18446744073709551616", -1, CTX_INVALID_PARAMETER_VALUE); // 2^64

  test_set_param(params, name, "xxxxxx", -1, CTX_INVALID_PARAMETER_VALUE);
}



/*
 * Branching parameter
 */
static void test_set_branching(param_t *params, const char *name) {
  uint32_t i;

  for (i=0; i<NUM_BRANCHING_MODES; i++) {
    test_set_param(params, name, branching2string[i], 0, 0);
  }

  test_set_param(params, name, "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);
}



/*
 * Tests of set_param
 */
static void test_set_params(param_t *params) {
  test_set_bool_param(params, "cache-tclauses");
  test_set_bool_param(params, "dyn-ack");
  test_set_bool_param(params, "dyn-bool-ack");
  test_set_bool_param(params, "fast-restarts");
  test_set_bool_param(params, "icheck");
  test_set_bool_param(params, "simplex-adjust");
  test_set_bool_param(params, "simplex-prop");

  test_set_posint_param(params, "aux-eq-quota");
  test_set_posint_param(params, "bland-threshold");
  test_set_posint_param(params, "c-threshold");
  test_set_posint_param(params, "d-threshold");
  test_set_posint_param(params, "icheck-period");
  test_set_posint_param(params, "max-ack");
  test_set_posint_param(params, "max-bool-ack");
  test_set_posint_param(params, "max-extensionality");
  test_set_posint_param(params, "max-interface-eqs");
  test_set_posint_param(params, "max-update-conflicts");
  test_set_posint_param(params, "r-initial-threshold");
  test_set_posint_param(params, "r-interval");

  test_set_posint2_param(params, "tclause-size");

  test_set_nonnegint_param(params, "prop-threshold");

  test_set_posint16_param(params, "dyn-ack-threshold");
  test_set_posint16_param(params, "dyn-bool-ack-threshold");

  test_set_uint32_pram(params, "random-seed");

  test_set_branching(params, "branching");

  test_set_param(params, "xxxx", "yyyy", -1, CTX_UNKNOWN_PARAMETER);
}


int main(void) {
  param_t *p1, *p2;

  yices_init();
  p1 = yices_new_param_record();
  printf("Allocated param record %p\n", p1);
  show_params(p1);

  p2 = yices_new_param_record();
  printf("Allocated param record %p\n", p2);
  show_params(p2);

  test_set_params(p2);

  yices_free_param_record(p2);
  yices_free_param_record(p1);

  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
