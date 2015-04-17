/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST CONTEXT CONFIGURATION FUNCTIONS
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "api/context_config.h"

#include "yices.h"


/*
 * Conversion of internal codes to strings
 */
static const char* const mode2string[NUM_MODES] = {
  "one-shot",          // CTX_MODE_ONECHECK
  "multi-checks",      // CTX_MODE_MULTICHECKS
  "push-pop",          // CTX_MODE_PUSHPOP
  "interactive",       // CTX_MODE_INTERACTIVE
};

static const char* const logic2string[NUM_SMT_LOGICS+1] = {
  "NONE",

  "AX",
  "BV",
  "IDL",
  "LIA",
  "LRA",
  "LIRA",
  "NIA",
  "NRA",
  "NIRA",
  "RDL",
  "UF",
  "ABV",
  "ALIA",
  "ALRA",
  "ALIRA",
  "ANIA",
  "ANRA",
  "ANIRA",
  "AUF",
  "UFBV",
  "UFIDL",
  "UFLIA",
  "UFLRA",
  "UFLIRA",
  "UFNIA",
  "UFNRA",
  "UFNIRA",
  "UFRDL",
  "AUFBV",
  "AUFLIA",
  "AUFLRA",
  "AUFLIRA",
  "AUFNIA",
  "AUFNRA",
  "AUFNIRA",

  "QF_AX",
  "QF_BV",
  "QF_IDL",
  "QF_RDL",
  "QF_LIA",
  "QF_LRA",
  "QF_LIRA",
  "QF_NIA",
  "QF_NRA",
  "QF_NIRA",
  "QF_UF",
  "QF_ABV",
  "QF_ALIA",
  "QF_ALRA",
  "QF_ALIRA",
  "QF_ANIA",
  "QF_ANRA",
  "QF_ANIRA",
  "QF_AUF",
  "QF_UFBV",
  "QF_UFIDL",
  "QF_UFLIA",
  "QF_UFLRA",
  "QF_UFLIRA",
  "QF_UFNIA",
  "QF_UFNRA",
  "QF_UFNIRA",
  "QF_UFRDL",
  "QF_AUFBV",
  "QF_AUFLIA",
  "QF_AUFLRA",
  "QF_AUFLIRA",
  "QF_AUFNIA",
  "QF_AUFNRA",
  "QF_AUFNIRA",

  "unknown",
};

static const char* const solver_code2string[NUM_SOLVER_CODES] = {
  "none",
  "default",
  "auto",
  "simplex",
  "ifw",
  "rfw",
};



/*
 * Which logics are currently supported
 */
static const bool supported[NUM_SMT_LOGICS] = {
  true,    // NONE

  false,   // AX
  false,   // BV
  false,   // IDL
  false,   // LIA
  false,   // LRA
  false,   // LIRA
  false,   // NIA
  false,   // NRA
  false,   // NIRA
  false,   // RDL
  false,   // UF
  false,   // ABV
  false,   // ALIA
  false,   // ALRA
  false,   // ALIRA
  false,   // ANIA
  false,   // ANRA
  false,   // ANIRA
  false,   // AUF
  false,   // UFBV
  false,   // UFIDL
  false,   // UFLIA
  false,   // UFLRA
  false,   // UFLIRA
  false,   // UFNIA
  false,   // UFNRA
  false,   // UFNIRA
  false,   // UFRDL
  false,   // AUFBV
  false,   // AUFLIA
  false,   // AUFLRA
  false,   // AUFLIRA
  false,   // AUFNIA
  false,   // AUFNRA
  false,   // AUFNIRA

  true,    // QF_AX
  true,    // QF_BV
  true,    // QF_IDL
  true,    // QF_RDL
  true,    // QF_LIA
  true,    // QF_LRA
  true,    // QF_LIRA
  false,   // QF_NIA
  false,   // QF_NRA
  false,   // QF_NIRA
  true,    // QF_UF
  true,    // QF_ABV
  true,    // QF_ALIA
  true,    // QF_ALRA
  true,    // QF_ALIRA
  false,   // QF_ANIA
  false,   // QF_ANRA
  false,   // QF_ANIRA
  true,    // QF_AUF
  true,    // QF_UFBV
  true,    // QF_UFIDL
  true,    // QF_UFLIA
  true,    // QF_UFLRA
  true,    // QF_UFLIRA
  false,   // QF_UFNIA
  false,   // QF_UFNRA
  false,   // QF_UFNIRA
  true,    // QF_UFRDL
  true,    // QF_AUFBV
  true,    // QF_AUFLIA
  true,    // QF_AUFLRA
  true,    // QF_AUFLIRA
  false,   // QF_AUFNIA
  false,   // QF_AUFNRA
  false,   // QF_AUFNIRA
};



/*
 * Print a configuration descriptor
 */
static void show_config(ctx_config_t *config) {
  printf("config: %p\n", config);
  printf("  mode =  %s\n", mode2string[config->mode]);
  printf("  logic = %s\n", logic2string[config->logic]);
  printf("  uf solver = %s\n", solver_code2string[config->uf_config]);
  printf("  array solver = %s\n", solver_code2string[config->array_config]);
  printf("  bv solver = %s\n", solver_code2string[config->bv_config]);
  printf("  arith solver = %s\n", solver_code2string[config->arith_config]);
  printf("\n");
  fflush(stdout);
}





/*
 * Test of default_config_for_logic:
 * - name = logic name to test
 * - k = expected returned value from the yices function
 * - error = expected error code (if k < 0)
 */
static void test_config_for_logic(ctx_config_t *config, const char *name, int32_t k, int32_t error) {
  int32_t code;
  error_code_t ecode;

  yices_clear_error();

  printf("Testing config for logic %s: ", name);
  fflush(stdout);
  code = yices_default_config_for_logic(config, name);
  if (code >= 0) {
    printf("ok\n");
    show_config(config);
  } else {
    printf("error\n");
    yices_print_error(stdout);
  }

  if (code != k) {
    printf("TEST FAILEDn");
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
 * Test of set_config:
 * - name = test parameter name
 * - value = test value
 * - k = expected returned value
 * - error = expected error code (if k < 0)
 */
static void test_set_config(ctx_config_t *config, const char *name, const char *value, int32_t k, int32_t error) {
  int32_t code;
  error_code_t ecode;

  printf("Testing set_config %s := %s: ", name, value);
  fflush(stdout);
  code = yices_set_config(config, name, value);
  if (code >= 0) {
    printf("ok\n");
    show_config(config);
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
 * Tests of config for logic
 */
static void test_logic_configs(ctx_config_t *config) {
  uint32_t i;

  // all valid logic names first
  for (i=0; i<NUM_SMT_LOGICS; i++) {
    if (supported[i]) {
      test_config_for_logic(config, logic2string[i], 0, 0);
    } else {
      test_config_for_logic(config, logic2string[i], -1, CTX_LOGIC_NOT_SUPPORTED);
    }
  }

  // some random stuff
  test_config_for_logic(config, "XXX", -1, CTX_UNKNOWN_LOGIC);
  test_config_for_logic(config, "unknown", -1, CTX_UNKNOWN_LOGIC);
}



/*
 * Tests of set config
 */
static void test_set_configs(ctx_config_t *config) {
  test_set_config(config, "mode", "one-shot", 0, 0);
  test_set_config(config, "mode", "multi-checks", 0, 0);
  test_set_config(config, "mode", "push-pop", 0, 0);
  test_set_config(config, "mode", "interactive", 0, 0);
  test_set_config(config, "mode", "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_config(config, "uf-solver", "default", 0, 0);
  test_set_config(config, "uf-solver", "none", 0, 0);
  test_set_config(config, "uf-solver", "simplex", -1, CTX_INVALID_PARAMETER_VALUE);
  test_set_config(config, "uf-solver", "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_config(config, "array-solver", "default", 0, 0);
  test_set_config(config, "array-solver", "none", 0, 0);
  test_set_config(config, "array-solver", "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_config(config, "bv-solver", "default", 0, 0);
  test_set_config(config, "bv-solver", "none", 0, 0);
  test_set_config(config, "bv-solver", "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);

  test_set_config(config, "arith-solver", "default", 0, 0);
  test_set_config(config, "arith-solver", "none", 0, 0);
  test_set_config(config, "arith-solver", "auto", 0, 0);
  test_set_config(config, "arith-solver", "simplex", 0, 0);
  test_set_config(config, "arith-solver", "ifw", 0, 0);
  test_set_config(config, "arith-solver", "rfw", 0, 0);
  test_set_config(config, "arith-solver", "xxxx", -1, CTX_INVALID_PARAMETER_VALUE);

  // yices_set_config is not intended to be used for setting the logic
  // so "logic" should not be recognized as a value parameter here.
  test_set_config(config, "logic", "QF_UFLIA", -1, CTX_UNKNOWN_PARAMETER);
}


int main(void) {
  ctx_config_t *c1, *c2;

  yices_init();
  c1 = yices_new_config();
  printf("Allocated config %p\n", c1);
  show_config(c1);

  c2 = yices_new_config();
  printf("Allocated config %p\n", c2);
  show_config(c2);

  test_logic_configs(c1);
  test_set_configs(c2);

  yices_free_config(c2);
  yices_free_config(c1);

  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
