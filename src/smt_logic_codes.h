/*
 * Codes for SMT Logic categories
 * - as of July 2011
 */

#ifndef __SMT_LOGIC_CODES_H
#define __SMT_LOGIC_CODES_H

/*
 * Codes for the logic (based on benchmarks available in June 2009)
 * + one special code 'NONE' for propositional logic
 *
 * 06/03/2014: More surprise logics for SMTCOMP 2014
 */
typedef enum smt_logic {
  NONE,        // added 12/27/2012

  ALIA,        // SMTCOMP 2014
  AUFLIA,
  AUFLIRA,
  AUFNIRA,
  BV,          // SMTCOMP 2014
  LIA,         // SMTCOMP 2014
  LRA,
  NIA,         // SMPCOMP 2014
  NRA,         // SMPCOMP 2014

  QF_ABV,      // new name for what used to be QF_AUFBV (arrays + BV)
  QF_ALIA,     // SMTCOMP 2014
  QF_AUFBV,    // now means arrays + uninterpreted functions + BV
  QF_AUFLIA,
  QF_AX,
  QF_BV,
  QF_IDL,
  QF_LIA,
  QF_LIRA,     // added 06/03/2014
  QF_LRA,
  QF_NIA,
  QF_NRA,      // added 07/25/2011
  QF_RDL,
  QF_UF,
  QF_UFBV,
  QF_UFIDL,
  QF_UFLIA,
  QF_UFLRA,
  QF_UFNIA,    // SMTCOMP 2014
  QF_UFNRA,

  UF,          // SMTCOMP 2014
  UFBV,        // SMTCOMP 2014
  UFIDL,       // SMTCOMP 2014
  UFLIA,       // SMTCOMP 2014
  UFLRA,       // added 07/25/2011
  UFNIA,

  SMT_UNKNOWN, // error code
} smt_logic_t;

// number of known SMT logics
#define NUM_SMT_LOGICS SMT_UNKNOWN


/*
 * Convert a logic name to an smt_logic code
 * return SMT_UNKNOWN if the name is not recognized
 */
extern smt_logic_t smt_logic_code(const char *logic_name);


#endif /* __SMT_LOGIC_CODES_H */
