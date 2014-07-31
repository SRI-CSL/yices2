/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>

#include "api/smt_logic_codes.h"

#define NUM_TESTS (NUM_SMT_LOGICS+6)

static const char * const test_names[NUM_TESTS] = {
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
  "",
  "badname",
  "ZZZZZZ",
  "QF_BBBBB",
  "AXXX",
  "QF_AX   ",
};

static const char *const code2string[NUM_SMT_LOGICS+1] = {
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
  "UNKNOWN"
};

int main() {
  uint32_t i;
  smt_logic_t code;

  for (i=0; i<NUM_SMT_LOGICS; i++) {
    printf("Testing '%s'\n", test_names[i]);
    code = smt_logic_code(test_names[i]);
    printf("code = %"PRId32": %s\n\n", (int32_t) code, code2string[code]);
    if (strcmp(test_names[i], code2string[code]) != 0) {
      printf("BUG: smt_logic_code didn't return the right code\n");
      exit(1);
    }
  }

  for (i=NUM_SMT_LOGICS; i<NUM_TESTS; i++) {
    printf("Testing '%s'\n", test_names[i]);
    code = smt_logic_code(test_names[i]);
    printf("code = %"PRId32": %s\n\n", (int32_t) code, code2string[code]);
    if (code != SMT_UNKNOWN) {
      printf("BUG: smt_logic_code didn't return SMT_UNKNOWN\n");
      exit(1);
    }
  }

  printf("All tests succeeded\n");
  fflush(stdout);

  return 0;
}

