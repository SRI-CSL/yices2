/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONVERSION FROM AN SMT LOGIC NAME TO AN INTEGER CODE
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
  "ABV",
  "ALIA",
  "ALIRA",
  "ALRA",
  "ANIA",
  "ANIRA",
  "ANRA",
  "AUF",
  "AUFBV",
  "AUFLIA",
  "AUFLIRA",
  "AUFLRA",
  "AUFNIA",
  "AUFNIRA",
  "AUFNRA",
  "AX",
  "BV",
  "IDL",
  "LIA",
  "LIRA",
  "LRA",
  "NIA",
  "NIRA",
  "NONE",
  "NRA",
  "QF_ABV",
  "QF_ALIA",
  "QF_ALIRA",
  "QF_ALRA",
  "QF_ANIA",
  "QF_ANIRA",
  "QF_ANRA",
  "QF_AUF",
  "QF_AUFBV",
  "QF_AUFLIA",
  "QF_AUFLIRA",
  "QF_AUFLRA",
  "QF_AUFNIA",
  "QF_AUFNIRA",
  "QF_AUFNRA",
  "QF_AX",
  "QF_BV",
  "QF_IDL",
  "QF_LIA",
  "QF_LIRA",
  "QF_LRA",
  "QF_NIA",
  "QF_NIRA",
  "QF_NRA",
  "QF_RDL",
  "QF_UF",
  "QF_UFBV",
  "QF_UFIDL",
  "QF_UFLIA",
  "QF_UFLIRA",
  "QF_UFLRA",
  "QF_UFNIA",
  "QF_UFNIRA",
  "QF_UFNRA",
  "QF_UFRDL",
  "RDL",
  "UF",
  "UFBV",
  "UFIDL",
  "UFLIA",
  "UFLIRA",
  "UFLRA",
  "UFNIA",
  "UFNIRA",
  "UFNRA",
  "UFRDL",
};


/*
 * Code table: smt_code[i] = code for smt_logic_name[i]
 * - for now, this is not very useful, but it may help later if
 *   different names correspond to the same logic
 */
static const smt_logic_t smt_code[NUM_SMT_LOGIC_NAMES] = {
  ABV,
  ALIA,
  ALIRA,
  ALRA,
  ANIA,
  ANIRA,
  ANRA,
  AUF,
  AUFBV,
  AUFLIA,
  AUFLIRA,
  AUFLRA,
  AUFNIA,
  AUFNIRA,
  AUFNRA,
  AX,
  BV,
  IDL,
  LIA,
  LIRA,
  LRA,
  NIA,
  NIRA,
  NONE,
  NRA,
  QF_ABV,
  QF_ALIA,
  QF_ALIRA,
  QF_ALRA,
  QF_ANIA,
  QF_ANIRA,
  QF_ANRA,
  QF_AUF,
  QF_AUFBV,
  QF_AUFLIA,
  QF_AUFLIRA,
  QF_AUFLRA,
  QF_AUFNIA,
  QF_AUFNIRA,
  QF_AUFNRA,
  QF_AX,
  QF_BV,
  QF_IDL,
  QF_LIA,
  QF_LIRA,
  QF_LRA,
  QF_NIA,
  QF_NIRA,
  QF_NRA,
  QF_RDL,
  QF_UF,
  QF_UFBV,
  QF_UFIDL,
  QF_UFLIA,
  QF_UFLIRA,
  QF_UFLRA,
  QF_UFNIA,
  QF_UFNIRA,
  QF_UFNRA,
  QF_UFRDL,
  RDL,
  UF,
  UFBV,
  UFIDL,
  UFLIA,
  UFLIRA,
  UFLRA,
  UFNIA,
  UFNIRA,
  UFNRA,
  UFRDL,
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


/*
 * Arithmetic fragments: names in lexicographic order
 */
static const char * const fragment_names[NUM_ARITH_FRAGMENTS] = {
  "IDL",
  "LIA",
  "LIRA",
  "LRA",
  "NIA",
  "NIRA",
  "NRA",
  "RDL",
};

static const arith_fragment_t fragment_code[NUM_ARITH_FRAGMENTS] = {
  ARITH_IDL,
  ARITH_LIA,
  ARITH_LIRA,
  ARITH_LRA,
  ARITH_NIA,
  ARITH_NIRA,
  ARITH_NRA,
  ARITH_RDL,
};


// search in these tables
arith_fragment_t arith_fragment_code(const char *name) {
  uint32_t l, h, k;
  int cmp;

  l = 0;
  h = NUM_ARITH_FRAGMENTS;

  for (;;) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    cmp = strcmp(name, fragment_names[k]);
    if (cmp == 0) return fragment_code[k];
    if (k == l) return ARITH_NONE;
    if (cmp < 0) {
      h = k;
    } else {
      assert(cmp > 0);
      l = k;
    }
  }
}


/*
 * Mapping from logic code to features/theories
 */
static const uint8_t has_arrays[NUM_SMT_LOGICS] = {
  false,  // NONE

  true,   // AX
  false,  // BV
  false,  // IDL
  false,  // LIA
  false,  // LRA
  false,  // LIRA
  false,  // NIA
  false,  // NRA
  false,  // NIRA
  false,  // RDL
  false,  // UF
  true,   // ABV
  true,   // ALIA
  true,   // ALRA
  true,   // ALIRA
  true,   // ANIA
  true,   // ANRA
  true,   // ANIRA
  true,   // AUF
  false,  // UFBV
  false,  // UFIDL
  false,  // UFLIA
  false,  // UFLRA
  false,  // UFLIRA
  false,  // UFNIA
  false,  // UFNRA
  false,  // UFNIRA
  false,  // UFRDL
  true,   // AUFBV
  true,   // AUFLIA
  true,   // AUFLRA
  true,   // AUFLIRA
  true,   // AUFNIA
  true,   // AUFNRA
  true,   // AUFNIRA

  true,   // QF_AX
  false,  // QF_BV
  false,  // QF_IDL
  false,  // QF_LIA
  false,  // QF_LRA
  false,  // QF_LIRA
  false,  // QF_NIA
  false,  // QF_NRA
  false,  // QF_NIRA
  false,  // QF_RDL
  false,  // QF_UF
  true,   // QF_ABV
  true,   // QF_ALIA
  true,   // QF_ALRA
  true,   // QF_ALIRA
  true,   // QF_ANIA
  true,   // QF_ANRA
  true,   // QF_ANIRA
  true,   // QF_AUF
  false,  // QF_UFBV
  false,  // QF_UFIDL
  false,  // QF_UFLIA
  false,  // QF_UFLRA
  false,  // QF_UFLIRA
  false,  // QF_UFNIA
  false,  // QF_UFNRA
  false,  // QF_UFNIRA
  false,  // QF_UFRDL
  true,   // QF_AUFBV
  true,   // QF_AUFLIA
  true,   // QF_AUFLRA
  true,   // QF_AUFLIRA
  true,   // QF_AUFNIA
  true,   // QF_AUFNRA
  true,   // QF_AUFNIRA
};

static const uint8_t has_bv[NUM_SMT_LOGICS] = {
  false,  // NONE

  false,  // AX
  true,   // BV
  false,  // IDL
  false,  // LIA
  false,  // LRA
  false,  // LIRA
  false,  // NIA
  false,  // NRA
  false,  // NIRA
  false,  // RDL
  false,  // UF
  true,   // ABV
  false,  // ALIA
  false,  // ALRA
  false,  // ALIRA
  false,  // ANIA
  false,  // ANRA
  false,  // ANIRA
  false,  // AUF
  true,   // UFBV
  false,  // UFIDL
  false,  // UFLIA
  false,  // UFLRA
  false,  // UFLIRA
  false,  // UFNIA
  false,  // UFNRA
  false,  // UFNIRA
  false,  // UFRDL
  true,   // AUFBV
  false,  // AUFLIA
  false,  // AUFLRA
  false,  // AUFLIRA
  false,  // AUFNIA
  false,  // AUFNRA
  false,  // AUFNIRA

  false,  // QF_AX
  true,   // QF_BV
  false,  // QF_IDL
  false,  // QF_LIA
  false,  // QF_LRA
  false,  // QF_LIRA
  false,  // QF_NIA
  false,  // QF_NRA
  false,  // QF_NIRA
  false,  // QF_RDL
  false,  // QF_UF
  true,   // QF_ABV
  false,  // QF_ALIA
  false,  // QF_ALRA
  false,  // QF_ALIRA
  false,  // QF_ANIA
  false,  // QF_ANRA
  false,  // QF_ANIRA
  false,  // QF_AUF
  true,   // QF_UFBV
  false,  // QF_UFIDL
  false,  // QF_UFLIA
  false,  // QF_UFLRA
  false,  // QF_UFLIRA
  false,  // QF_UFNIA
  false,  // QF_UFNRA
  false,  // QF_UFNIRA
  false,  // QF_UFRDL
  true,   // QF_AUFBV
  false,  // QF_AUFLIA
  false,  // QF_AUFLRA
  false,  // QF_AUFLIRA
  false,  // QF_AUFNIA
  false,  // QF_AUFNRA
  false,  // QF_AUFNIRA
};

static const uint8_t has_quantifiers[NUM_SMT_LOGICS] = {
  false,  // NONE

  true,   // AX
  true,   // BV
  true,   // IDL
  true,   // LIA
  true,   // LRA
  true,   // LIRA
  true,   // NIA
  true,   // NRA
  true,   // NIRA
  true,   // RDL
  true,   // UF
  true,   // ABV
  true,   // ALIA
  true,   // ALRA
  true,   // ALIRA
  true,   // ANIA
  true,   // ANRA
  true,   // ANIRA
  true,   // AUF
  true,   // UFBV
  true,   // UFIDL
  true,   // UFLIA
  true,   // UFLRA
  true,   // UFLIRA
  true,   // UFNIA
  true,   // UFNRA
  true,   // UFNIRA
  true,   // UFRDL
  true,   // AUFBV
  true,   // AUFLIA
  true,   // AUFLRA
  true,   // AUFLIRA
  true,   // AUFNIA
  true,   // AUFNRA
  true,   // AUFNIRA

  false,  // QF_AX
  false,  // QF_BV
  false,  // QF_IDL
  false,  // QF_LIA
  false,  // QF_LRA
  false,  // QF_LIRA
  false,  // QF_NIA
  false,  // QF_NRA
  false,  // QF_NIRA
  false,  // QF_RDL
  false,  // QF_UF
  false,  // QF_ABV
  false,  // QF_ALIA
  false,  // QF_ALRA
  false,  // QF_ALIRA
  false,  // QF_ANIA
  false,  // QF_ANRA
  false,  // QF_ANIRA
  false,  // QF_AUF
  false,  // QF_UFBV
  false,  // QF_UFIDL
  false,  // QF_UFLIA
  false,  // QF_UFLRA
  false,  // QF_UFLIRA
  false,  // QF_UFNIA
  false,  // QF_UFNRA
  false,  // QF_UFNIRA
  false,  // QF_UFRDL
  false,  // QF_AUFBV
  false,  // QF_AUFLIA
  false,  // QF_AUFLRA
  false,  // QF_AUFLIRA
  false,  // QF_AUFNIA
  false,  // QF_AUFNRA
  false,  // QF_AUFNIRA
};

static const uint8_t has_uf[NUM_SMT_LOGICS] = {
  false,  // NONE

  false,  // AX
  false,  // BV
  false,  // IDL
  false,  // LIA
  false,  // LRA
  false,  // LIRA
  false,  // NIA
  false,  // NRA
  false,  // NIRA
  false,  // RDL
  true,   // UF
  false,  // ABV
  false,  // ALIA
  false,  // ALRA
  false,  // ALIRA
  false,  // ANIA
  false,  // ANRA
  false,  // ANIRA
  true,   // AUF
  true,   // UFBV
  true,   // UFIDL
  true,   // UFLIA
  true,   // UFLRA
  true,   // UFLIRA
  true,   // UFNIA
  true,   // UFNRA
  true,   // UFNIRA
  true,   // UFRDL
  true,   // AUFBV
  true,   // AUFLIA
  true,   // AUFLRA
  true,   // AUFLIRA
  true,   // AUFNIA
  true,   // AUFNRA
  true,   // AUFNIRA

  false,  // QF_AX
  false,  // QF_BV
  false,  // QF_IDL
  false,  // QF_LIA
  false,  // QF_LRA
  false,  // QF_LIRA
  false,  // QF_NIA
  false,  // QF_NRA
  false,  // QF_NIRA
  false,  // QF_RDL
  true,   // QF_UF
  false,  // QF_ABV
  false,  // QF_ALIA
  false,  // QF_ALRA
  false,  // QF_ALIRA
  false,  // QF_ANIA
  false,  // QF_ANRA
  false,  // QF_ANIRA
  true,   // QF_AUF
  true,   // QF_UFBV
  true,   // QF_UFIDL
  true,   // QF_UFLIA
  true,   // QF_UFLRA
  true,   // QF_UFLIRA
  true,   // QF_UFNIA
  true,   // QF_UFNRA
  true,   // QF_UFNIRA
  true,   // QF_UFRDL
  true,   // QF_AUFBV
  true,   // QF_AUFLIA
  true,   // QF_AUFLRA
  true,   // QF_AUFLIRA
  true,   // QF_AUFNIA
  true,   // QF_AUFNRA
  true,   // QF_AUFNIRA
};

static const uint8_t arith_frag[NUM_SMT_LOGICS] = {
  ARITH_NONE,   // NONE

  ARITH_NONE,   // AX
  ARITH_NONE,   // BV
  ARITH_IDL,    // IDL
  ARITH_LIA,    // LIA
  ARITH_LRA,    // LRA
  ARITH_LIRA,   // LIRA
  ARITH_NIA,    // NIA
  ARITH_NRA,    // NRA
  ARITH_NIRA,   // NIRA
  ARITH_RDL,    // RDL
  ARITH_NONE,   // UF
  ARITH_NONE,   // ABV
  ARITH_LIA,    // ALIA
  ARITH_LRA,    // ALRA
  ARITH_LIRA,   // ALIRA
  ARITH_NIA,    // ANIA
  ARITH_NRA,    // ANRA
  ARITH_NIRA,   // ANIRA
  ARITH_NONE,   // AUF
  ARITH_NONE,   // UFBV
  ARITH_IDL,    // UFIDL
  ARITH_LIA,    // UFLIA
  ARITH_LRA,    // UFLRA
  ARITH_LIRA,   // UFLIRA
  ARITH_NIA,    // UFNIA
  ARITH_NRA,    // UFNRA
  ARITH_NIRA,   // UFNIRA
  ARITH_RDL,    // UFRDL
  ARITH_NONE,   // AUFBV
  ARITH_LIA,    // AUFLIA
  ARITH_LRA,    // AUFLRA
  ARITH_LIRA,   // AUFLIRA
  ARITH_NIA,    // AUFNIA
  ARITH_NRA,    // AUFNRA
  ARITH_NIRA,   // AUFNIRA

  ARITH_NONE,   // QF_AX
  ARITH_NONE,   // QF_BV
  ARITH_IDL,    // QF_IDL
  ARITH_LIA,    // QF_LIA
  ARITH_LRA,    // QF_LRA
  ARITH_LIRA,   // QF_LIRA
  ARITH_NIA,    // QF_NIA
  ARITH_NRA,    // QF_NRA
  ARITH_NIRA,   // QF_NIRA
  ARITH_RDL,    // QF_RDL
  ARITH_NONE,   // QF_UF
  ARITH_NONE,   // QF_ABV
  ARITH_LIA,    // QF_ALIA
  ARITH_LRA,    // QF_ALRA
  ARITH_LIRA,   // QF_ALIRA
  ARITH_NIA,    // QF_ANIA
  ARITH_NRA,    // QF_ANRA
  ARITH_NIRA,   // QF_ANIRA
  ARITH_NONE,   // QF_AUF
  ARITH_NONE,   // QF_UFBV
  ARITH_IDL,    // QF_UFIDL
  ARITH_LIA,    // QF_UFLIA
  ARITH_LRA,    // QF_UFLRA
  ARITH_LIRA,   // QF_UFLIRA
  ARITH_NIA,    // QF_UFNIA
  ARITH_NRA,    // QF_UFNRA
  ARITH_NIRA,   // QF_UFNIRA
  ARITH_RDL,    // QF_UFRDL
  ARITH_NONE,   // QF_AUFBV
  ARITH_LIA,    // QF_AUFLIA
  ARITH_LRA,    // QF_AUFLRA
  ARITH_LIRA,   // QF_AUFLIRA
  ARITH_NIA,    // QF_AUFNIA
  ARITH_NRA,    // QF_AUFNRA
  ARITH_NIRA,   // QF_AUFNIRA
};


/*
 * Check features of a logic
 */
bool logic_has_arrays(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return has_arrays[code];
}

bool logic_has_arith(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return arith_frag[code] != ARITH_NONE;
}

bool logic_has_bv(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return has_bv[code];
}

bool logic_has_quantifiers(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return has_quantifiers[code];
}

bool logic_has_uf(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return has_uf[code];
}

arith_fragment_t arith_fragment(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return arith_frag[code];
}


/*
 * Which of these are officially recognized by our masters.
 *
 * - 2014/06/19: marked as 'official' everything in SMT-COMP 2014
 */
static const bool is_official[NUM_SMT_LOGICS] = {
  false,  // NONE

  false,  // AX
  true,   // BV
  false,  // IDL
  true,   // LIA
  true,   // LRA
  false,  // LIRA
  true,   // NIA
  true,   // NRA
  false,  // NIRA
  false,  // RDL
  true,   // UF
  false,  // ABV
  true,   // ALIA
  false,  // ALRA
  false,  // ALIRA
  false,  // ANIA
  false,  // ANRA
  false,  // ANIRA
  false,  // AUF
  true,   // UFBV
  true,   // UFIDL
  true,   // UFLIA
  true,   // UFLRA
  false,  // UFLIRA
  true,   // UFNIA
  false,  // UFNRA
  false,  // UFNIRA
  false,  // UFRDL
  false,  // AUFBV
  true,   // AUFLIA
  false,  // AUFLRA
  true,   // AUFLIRA
  false,  // AUFNIA
  false,  // AUFNRA
  true,   // AUFNIRA

  true,   // QF_AX
  true,   // QF_BV
  true,   // QF_IDL
  true,   // QF_LIA
  true,   // QF_LRA
  false,  // QF_LIRA
  true,   // QF_NIA
  true,   // QF_NRA
  false,  // QF_NIRA
  true,   // QF_RDL
  true,   // QF_UF
  true,   // QF_ABV
  true,   // QF_ALIA
  false,  // QF_ALRA
  false,  // QF_ALIRA
  false,  // QF_ANIA
  false,  // QF_ANRA
  false,  // QF_ANIRA
  false,  // QF_AUF
  true,   // QF_UFBV
  true,   // QF_UFIDL
  true,   // QF_UFLIA
  true,   // QF_UFLRA
  false,  // QF_UFLIRA
  true,   // QF_UFNIA
  true,   // QF_UFNRA
  false,  // QF_UFNIRA
  false,  // QF_UFRDL
  true,   // QF_AUFBV
  true,   // QF_AUFLIA
  false,  // QF_AUFLRA
  true,   // QF_AUFLIRA
  true,   // QF_AUFNIA
  true,   // QF_AUFNRA
  true,   // QF_AUFNIRA
};


bool logic_is_official(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return is_official[code];
}
