/*
 * Parser for benchmarks in the SMT-LIB language.
 */

#ifndef __SMT_PARSER_H
#define __SMT_PARSER_H

#include "parser.h"


/*
 * The result of parsing is stored in the following structure
 */
typedef enum smt_stat {
  smt_none,
  smt_unsat,
  smt_sat,
  smt_unknown,
} smt_stat_t;

typedef struct smt_benchmark_s {
  char *name;
  char *logic_name;
  int32_t logic_parameter; // used only for QF_UFBV[xx]
  smt_stat_t status;
  uint32_t nformulas; // number of formulas and assumptions
  uint32_t fsize;     // size of array formulas
  term_t *formulas;   // the corresponding terms
} smt_benchmark_t;



/*
 * Minimal size of formulas array (allocated on the first addition)
 */
#define MIN_FSIZE 20

/*
 * Maximal number of formulas
 */
#define MAX_FSIZE (UINT32_MAX/sizeof(term_t))


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
 * Initialize a benchmark structure (all fields are given a default value).
 */
extern void init_benchmark(smt_benchmark_t *bench);

/*
 * Delete: free all allocated memory
 */
extern void delete_benchmark(smt_benchmark_t *bench);

/*
 * return -1 if there's an error, 0 otherwise
 * if result is 0 then bench is filled in
 */
extern int32_t parse_smt_benchmark(parser_t *parser, smt_benchmark_t *bench);


/*
 * Convert a logic name to an smt_logic code
 * return SMT_UNKNOWN if the name is not recognized
 */
extern smt_logic_t smt_logic_code(const char *logic_name);



#endif /* __SMT_PARSER_H */
