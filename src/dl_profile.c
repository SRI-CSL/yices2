/*
 * Compute profile of SMT benchmarks in the DL fragments
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>
#include <gmp.h>

#include "smt_lexer.h"
#include "smt_parser.h"
#include "term_stack.h"
#include "term_printer.h"

#include "context.h"

#include "cputime.h"
#include "memsize.h"

#include "yices_version.h"
#include "yices_exit_codes.h"


/*
 * GLOBAL OBJECTS
 */

static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;
static context_t context;
static double construction_time;


/*
 * Conversion of status code in the benchmark header
 */
static const char * const status2string[] = {
  "none", "unsat", "sat", "unknown",  
};


/*
 * Conversion of internalization code to an error message
 */
static const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error", 
  "internal error",
  "type error",
  "formula contains free-variables",
  "logic not supported",
  "context does not support UF",
  "context does not support arithmetic",
  "context does not support bitvectors",
  "context does not support function equalities",
  "context does not support quantifiers",
  "context does not support lambdas",
  "not an IDL formula",
  "not an RDL formula",
  "formula is not in linear arithmetic",
  "too many arithmetic variables",
  "too many arithmetic atoms",
  "arithmetic solver exception",
  "bitvector solver exception",
};




/*
 * Filename given on the command line
 */
static char *filename;


/**********************************
 *  PRINT STATISTICS AND RESULTS  *
 *********************************/

/*
 * Benchmark header
 */
static void print_benchmark(FILE *f, smt_benchmark_t *bench) {
  uint32_t n;

  n = bench->nformulas;
  fprintf(f, "Benchmark: %s\n", bench->name);
  fprintf(f, "Logic: %s\n", bench->logic_name);
  fprintf(f, "Logic parameter: %"PRId32"\n", bench->logic_parameter);
  fprintf(f, "Status field: %s\n", status2string[bench->status]);
  fprintf(f, "Number of formulas or assumptions: %"PRIu32"\n\n", n);
}



/*
 * Statistics on problem size, before the search
 */
static void print_presearch_stats() {
  smt_core_t *core;
  egraph_t *egraph;

  core = context.core;
  egraph = context.egraph;


  printf("eliminated equalities   : %"PRIu32"\n", num_eliminated_eqs(&context));
  printf("subst candidates        : %"PRIu32"\n", num_subst_candidates(&context));
  printf("substitutions           : %"PRIu32"\n", num_substitutions(&context));
  printf("top equalities          : %"PRIu32"\n", num_top_eqs(&context));
  printf("top atoms               : %"PRIu32"\n", num_top_atoms(&context));
  printf("top formulas            : %"PRIu32"\n", num_top_formulas(&context));

  printf("boolean variables       : %"PRIu32"\n", core->nvars);
  printf("atoms                   : %"PRIu32"\n", core->atoms.natoms);
  if (egraph != NULL) {
    printf("egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
  }
  printf("\n");
  fflush(stdout);
}


/*
 * Print the translation code returned by assert
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("Assertions simplify to false\n\n"); 
  } else if (code < 0) {
    code = - code;
    if (code <= FORMULA_NOT_RDL) {
      printf("Internalization error: %s\n\n", code2error[code]);
    } else {
      printf("%s\n\n", code2error[code]);
    }
  }
}







/*
 * MAIN SOLVER FUNCTION
 * - parse input file (assumed to be in SMT-LIB format)
 * - solve benchmark
 * - return an exit code (defined in yices_exit_codes.h)
 */
static int process_benchmark(char *filename) {
  int32_t code;
  double mem_used;
  context_arch_t arch;
  
  if (init_smt_file_lexer(&lexer, filename) < 0) {
    perror(filename);
    return YICES_EXIT_FILE_NOT_FOUND;
  }

  /*
   * Parse and build the formula
   */
  yices_init();
  tstack_set_smt_mode();
  init_tstack(&stack);
  init_parser(&parser, &lexer, &stack);
  init_benchmark(&bench);
  code = parse_smt_benchmark(&parser, &bench);
  if (code < 0) {
    return YICES_EXIT_SYNTAX_ERROR;
  }

  construction_time = get_cpu_time();
  mem_used = mem_size() / (1024 * 1024);
  print_benchmark(stdout, &bench);
  printf("Construction time: %.4f s\n", construction_time);
  printf("Memory used: %.2f MB\n\n", mem_used);
  fflush(stdout);

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);

  /*
   * Select architecture based on the benchmark logic
   * - QF_IDL --> IDL Floyd Warshall
   * - QF_RDL --> RDL Floyd Warshall
   * other logics are not supported yet: no solver
   */
  arch = CTX_ARCH_NOSOLVERS;
  if (bench.logic_name != NULL) {
    if (strcmp(bench.logic_name, "QF_IDL") == 0) {
      arch = CTX_ARCH_IFW;
    } else if (strcmp(bench.logic_name, "QF_RDL") == 0) {
      arch = CTX_ARCH_RFW;
    }
  }

  /*
   * Initialize the context and set options
   */
  init_context(&context, CTX_MODE_ONECHECK, arch, false);

  /*
   *  Internalize
   */
  code = assert_formulas(&context, bench.nformulas, bench.formulas);
  print_internalization_code(code);
  print_presearch_stats();

  /*
   * Cleanup
   */
  delete_context(&context);
  delete_benchmark(&bench);
  yices_cleanup();

  return YICES_EXIT_SUCCESS;
}



int main(int argc, char *argv[]) {  
  if (argc != 2) {
    printf("Usage: %s <filename>\n", argv[0]);
  }
  filename = argv[1];
  return process_benchmark(filename);
}

