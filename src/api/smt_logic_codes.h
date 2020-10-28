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
 * CODES FOR THE SMT LOGICS
 */

#ifndef __SMT_LOGIC_CODES_H
#define __SMT_LOGIC_CODES_H

#include <stdbool.h>

/*
 * Codes for the logic (based on benchmarks available in June 2009)
 * + one special code 'NONE' for propositional logic
 *
 * 06/03/2014: More surprise logics for SMTCOMP 2014
 *
 * 06/18/2014: Attempt to be a bit more systematic
 * -----------------------------------------------
 * Added all the logics listed at smt-lib.org + a few more that should be there.
 *
 * The base theories are:
 *    AX: arrays
 *    BV: bitvectors
 *    UF: uninterpreted types and functions
 *  + arithmetic
 *
 * For arithmetic:
 * - the domain can be Int or Reals or Both (mixed arithmetic)
 * - the type of atoms can be
 *   difference logic
 *   linear equalities and inequalities
 *   non-linear equalities and inequalities (polynomials)
 * - this gives nine arithmetic variants, but the standard does not include
 *   mixed difference logic. So we have eight arithmetic codes:
 *   IDL, RDL, LIA, LRA, LIRA, NIA, NRA, NIRA
 *
 * AX + UF can be combined with BV and with one of the arithmetic fragments
 * (except that we don't have AIDL and ARDL?).
 *
 * Then, for each logic, we have a quantifier-free variant.
 */
typedef enum smt_logic {
  NONE,        // added 12/27/2012

  /*
   * Base logics (with quantifiers)
   */
  AX,          // arrays
  BV,          // bitvectors
  IDL,         // integer difference logic
  LIA,         // linear integer arithmetic
  LRA,         // linear real arithmetic
  LIRA,        // mixed linear arithmetic
  NIA,         // non-linear integer arithmetic
  NRA,         // non-linear real arithmetic
  NIRA,        // non-linear mixed arithmetic
  RDL,         // real difference logic
  UF,          // uninterpreted functions

  //  Arrays + some other theory
  ABV,         // arrays + bitvectors
  ALIA,        // arrays + linear integer arithmetic
  ALRA,        // arrays + linear real arithmetic
  ALIRA,       // arrays + mixed linear arithmetic
  ANIA,        // arrays + non-linear integer arithmetic
  ANRA,        // arrays + non-linear real arithmetic
  ANIRA,       // arrays + mixed/non-linear arithmetic
  AUF,         // arrays + uninterpreted functions

  //  Uninterpreted function + another theory
  UFBV,        // uninterpreted functions + bitvectors
  UFIDL,       // uninterpreted functions + integer difference logic
  UFLIA,       // uninterpreted functions + linear integer arithmetic
  UFLRA,       // uninterpreted functions + linear real arithmetic
  UFLIRA,      // uninterpreted functions + mixed linear arithmetic
  UFNIA,       // uninterpreted functions + non-linear integer arithmetic
  UFNRA,       // uninterpreted functions + non-linear real arithmetic
  UFNIRA,      // uninterpreted functions + mixed, non-linear arithmetic
  UFRDL,       // uninterpreted functions + real difference logic

  //  Arrays + uninterpreted functions + another theory
  AUFBV,       // arrays + uninterpreted functions + bitvectors
  AUFLIA,      // arrays + uninterpreted functions + linear integer arithmetic
  AUFLRA,      // arrays + uninterpreted functions + linear real arithmetic
  AUFLIRA,     // arrays + uninterpreted functions + mixed linear arithmetic
  AUFNIA,      // arrays + uninterpreted functions + non-linear integer arithmetic
  AUFNRA,      // arrays + uninterpreted functions + non-linear real arithmetic
  AUFNIRA,     // arrays + uninterpreted functions + mixed, non-linear arithmetic

  /*
   * Quantifier-free fragments
   */
  QF_AX,       // arrays
  QF_BV,       // bitvectors
  QF_IDL,      // integer difference logic
  QF_LIA,      // linear integer arithmetic
  QF_LRA,      // linear real arithmetic
  QF_LIRA,     // mixed linear arithmetic
  QF_NIA,      // non-linear integer arithmetic
  QF_NRA,      // non-linear real arithmetic
  QF_NIRA,     // non-linear mixed arithmetic
  QF_RDL,      // real difference logic
  QF_UF,       // uninterpreted functions

  //  Arrays + some other theory
  QF_ABV,      // arrays + bitvectors
  QF_ALIA,     // arrays + linear integer arithmetic
  QF_ALRA,     // arrays + linear real arithmetic
  QF_ALIRA,    // arrays + mixed linear arithmetic
  QF_ANIA,     // arrays + non-linear integer arithmetic
  QF_ANRA,     // arrays + non-linear real arithmetic
  QF_ANIRA,    // arrays + mixed/non-linear arithmetic
  QF_AUF,      // arrays + uninterpreted functions

  //  Uninterpreted function + another theory
  QF_UFBV,     // uninterpreted functions + bitvectors
  QF_UFIDL,    // uninterpreted functions + integer difference logic
  QF_UFLIA,    // uninterpreted functions + linear integer arithmetic
  QF_UFLRA,    // uninterpreted functions + linear real arithmetic
  QF_UFLIRA,   // uninterpreted functions + mixed linear arithmetic
  QF_UFNIA,    // uninterpreted functions + non-linear integer arithmetic
  QF_UFNRA,    // uninterpreted functions + non-linear real arithmetic
  QF_UFNIRA,   // uninterpreted functions + mixed, non-linear arithmetic
  QF_UFRDL,    // uninterpreted functions + real difference logic

  //  Arrays + uninterpreted functions + another theory
  QF_AUFBV,    // arrays + uninterpreted functions + bitvectors
  QF_AUFLIA,   // arrays + uninterpreted functions + linear integer arithmetic
  QF_AUFLRA,   // arrays + uninterpreted functions + linear real arithmetic
  QF_AUFLIRA,  // arrays + uninterpreted functions + mixed linear arithmetic
  QF_AUFNIA,   // arrays + uninterpreted functions + non-linear integer arithmetic
  QF_AUFNRA,   // arrays + uninterpreted functions + non-linear real arithmetic
  QF_AUFNIRA,  // arrays + uninterpreted functions + mixed, non-linear arithmetic

  /*
   * Added 2018/05/17: special code for the 'ALL' logic
   * as in (set-logic ALL).
   *
   * We interpret this a QF_AUFLIRA + QF_BV unless MCSAT is
   * enabled in which case it is QF_UFNIRA + QF_BV.
   */
  SMT_ALL,

  /*
   * Anything else is an error
   */
  SMT_UNKNOWN,
} smt_logic_t;

// number of known SMT logics
#define NUM_SMT_LOGICS ((uint32_t) SMT_UNKNOWN)


/*
 * Arithmetic fragments
 */
typedef enum arith_fragment {
  ARITH_IDL,   // integer difference logic
  ARITH_RDL,   // real difference logic
  ARITH_LIA,   // linear integer arithmetic
  ARITH_LRA,   // linear real arithmetic
  ARITH_LIRA,  // linear mixed arithmetic
  ARITH_NIA,   // non-linear integer arithmetic
  ARITH_NRA,   // non-linear real arithmetic
  ARITH_NIRA,  // non-linear mixed arithmetic
  ARITH_NONE,  // no arithmetic
} arith_fragment_t;

#define NUM_ARITH_FRAGMENTS ((uint32_t) ARITH_NONE)



/*
 * Convert a logic name to an smt_logic code
 * - the name is a string like "QF_UFLIA"
 * - return SMT_UNKNOWN if the name is not recognized
 */
extern smt_logic_t smt_logic_code(const char *logic_name);


/*
 * Convert a string to an arithmetic-fragment code
 * - the name must be something like "IDL" or "LIRA"
 * - return ARITH_NONE if the name is not recognized
 */
extern arith_fragment_t arith_fragment_code(const char *name);


/*
 * Queries on a logic
 * - check whether a logic includes a particular feature or theory
 * - code must be a valid logic code (not SMT_UNKNOWN)
 */
extern bool logic_has_arrays(smt_logic_t code);
extern bool logic_has_arith(smt_logic_t code);
extern bool logic_has_bv(smt_logic_t code);
extern bool logic_has_quantifiers(smt_logic_t code);
extern bool logic_has_uf(smt_logic_t code);


/*
 * Quantifier-free fragment of a logic:
 * - if code is for a quantifier-free logic, the function
 *   returns code unchanged
 * - if code is a quantified logic, this returns the QF variant
 *   (e.g., qf_fragment(AUFLIA) --> QF_AUFLIA).
 * - if code is SMT_UNKNOWN, this returns SMT_UNKNOWN
 */
extern smt_logic_t qf_fragment(smt_logic_t code);


/*
 * Arithmetic fragment for a given logic
 * - code must be a valid code (not SMT_UNKNOWN)
 * - return ARITH_NONE if the logic does not include arithmetic
 */
extern arith_fragment_t arith_fragment(smt_logic_t code);


/*
 * Check whether a logic code has been anointed by SMT-LIB as an
 * official logic. This changes with time.
 */
extern bool logic_is_official(smt_logic_t code);


#endif /* __SMT_LOGIC_CODES_H */
