/*
 * Conversion from SMT logic names to an integer code
 */

#include <stdint.h>
#include <string.h>
#include <assert.h>

#include "api/smt_logic_codes.h"

/*
 * Table of known logic names in lexicographic order
 */
#define NUM_SMT_LOGIC_NAMES NUM_SMT_LOGICS

static const char * const smt_logic_names[NUM_SMT_LOGIC_NAMES] = {
  "AUFLIA",
  "AUFLIRA",
  "AUFNIRA",
  "LRA",
  "NONE",
  "QF_ABV",
  "QF_AUFBV",
  "QF_AUFLIA",
  "QF_AX",
  "QF_BV",
  "QF_IDL",
  "QF_LIA",
  "QF_LRA",
  "QF_NIA",
  "QF_NRA",
  "QF_RDL",
  "QF_UF",
  "QF_UFBV",
  "QF_UFIDL",
  "QF_UFLIA",
  "QF_UFLRA",
  "QF_UFNRA",
  "UFLRA",
  "UFNIA",
};


/*
 * Code table: smt_code[i] = code for smt_logic_name[i]
 * - for now, this is not very useful, but it may help later if
 *   different names correspond to the same logic
 */
static const smt_logic_t smt_code[NUM_SMT_LOGIC_NAMES] = {
  AUFLIA,
  AUFLIRA,
  AUFNIRA,
  LRA,
  NONE,
  QF_ABV,
  QF_AUFBV,
  QF_AUFLIA,
  QF_AX,
  QF_BV,
  QF_IDL,
  QF_LIA,
  QF_LRA,
  QF_NIA,
  QF_NRA,
  QF_RDL,
  QF_UF,
  QF_UFBV,
  QF_UFIDL,
  QF_UFLIA,
  QF_UFLRA,
  QF_UFNRA,
  UFLRA,
  UFNIA,
};


/*
 * Binary search in the tables above
 */
smt_logic_t smt_logic_code(const char *logic_name) {
  uint32_t l, h, k;
  int cmp;

  l = 0;
  h = NUM_SMT_LOGIC_NAMES;

  for (;;) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    cmp = strcmp(logic_name, smt_logic_names[k]);
    if (cmp == 0) return smt_code[k];
    if (k == l) return SMT_UNKNOWN;
    if (cmp < 0) {
      h = k;
    } else {
      assert(cmp > 0);
      l = k;
    }
  }
}
