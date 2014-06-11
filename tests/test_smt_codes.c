#include <stdio.h>
#include <inttypes.h>

#include "smt_logic_codes.h"

#define NUM_TESTS 41

static const char * const test_names[NUM_TESTS] = {
  "NONE",
  "ALIA",
  "AUFLIA",
  "AUFLIRA",
  "AUFNIRA",
  "BV",
  "LIA",
  "LRA",
  "NIA",
  "NRA",
  "QF_ABV",
  "QF_ALIA",
  "QF_AUFBV",
  "QF_AUFLIA",
  "QF_AX",
  "QF_BV",
  "QF_IDL",
  "QF_LIA",
  "QF_LIRA",
  "QF_LRA",
  "QF_NIA",
  "QF_NRA",
  "QF_RDL",
  "QF_UF",
  "QF_UFBV",
  "QF_UFIDL",
  "QF_UFLIA",
  "QF_UFLRA",
  "QF_UFLIRA", 
  "QF_UFNIA",
  "QF_UFNRA",
  "UF",
  "UFBV",
  "UFIDL",
  "UFLIA",
  "UFLRA",
  "UFNIA",
  "",
  "badname",
  "ZZZZZZ",
  "QF_BBBBB",
  "AXXX",
};

static const char *const code2string[NUM_SMT_LOGICS+1] = {
  "NONE",
  "ALIA",
  "AUFLIA",
  "AUFLIRA",
  "AUFNIRA",
  "BV",
  "LIA",
  "LRA",
  "NIA",
  "NRA",
  "QF_ABV",
  "QF_ALIA",
  "QF_AUFBV",
  "QF_AUFLIA",
  "QF_AX",
  "QF_BV",
  "QF_IDL",
  "QF_LIA",
  "QF_LIRA",
  "QF_LRA",
  "QF_NIA",
  "QF_NRA",
  "QF_RDL",
  "QF_UF",
  "QF_UFBV",
  "QF_UFIDL",
  "QF_UFLIA",
  "QF_UFLRA",
  "QF_UFLIRA", 
  "QF_UFNIA",
  "QF_UFNRA",
  "UF",
  "UFBV",
  "UFIDL",
  "UFLIA",
  "UFLRA",
  "UFNIA",
  "SMT_UNKNOWN",
};

int main() {
  uint32_t i;
  smt_logic_t code;

  for (i=0; i<NUM_TESTS; i++) {
    printf("Testing %s\n", test_names[i]);
    code = smt_logic_code(test_names[i]);
    printf("code = %"PRId32": %s\n\n", (int32_t) code, code2string[code]);
  }

  return 0;
}

