/*
 * Codes for SMT Logic categories (as of June 2008)
 */

#ifndef __SMT_LOGIC_CODES_H
#define __SMT_LOGIC_CODES_H

/*
 * Codes for the logic (based on benchmarks available in June 2008)
 */
typedef enum smt_logic {
  AUFLIA,
  AUFLIRA,
  AUFNIRA,
  QF_AUFBV,
  QF_AUFLIA,
  QF_AX,
  QF_BV,
  QF_IDL,
  QF_LIA,
  QF_LRA,
  QF_RDL,
  QF_UF,
  QF_UFBV32,
  QF_UFIDL,
  QF_UFLIA,
  QF_UFLRA,
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
