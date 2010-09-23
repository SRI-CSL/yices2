/*
 * Codes for SMT Logic categories
 * - as of June 09
 */

#ifndef __SMT_LOGIC_CODES_H
#define __SMT_LOGIC_CODES_H

/*
 * Codes for the logic (based on benchmarks available in June 2009)
 */
typedef enum smt_logic {
  AUFLIA,
  AUFLIRA,
  AUFNIRA,
  LRA,
  QF_AUFBV,
  QF_AUFLIA,
  QF_AX,
  QF_BV,
  QF_IDL,
  QF_LIA,
  QF_LRA,
  QF_NIA,
  QF_RDL,
  QF_UF,
  QF_UFBV,
  QF_UFIDL,
  QF_UFLIA,
  QF_UFLRA,
  QF_UFNRA,
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
