/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parser for benchmarks in the SMT-LIB language.
 */

#ifndef __SMT_PARSER_H
#define __SMT_PARSER_H

#include "parser_utils/parser.h"


/*
 * The result of parsing is stored in the following structure:
 *
 * We keep track of whether any function or predicate is declared
 * (with non-zero arity). This helps detecting incorrect/misleading
 * logic labels (e.g. the bcnscheduling benchmarks are in QF_UFIDL but
 * they are actually pure QF_IDL. They don't have functions or
 * predicates.
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
  bool has_uf;        // true if the benchmark declares uninterpreted functions or predicates
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



#endif /* __SMT_PARSER_H */
