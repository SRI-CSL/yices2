#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>


#include "cputime.h"
#include "memsize.h"

#include "term_printer.h"
#include "type_printer.h"
#include "term_stack.h"
#include "smt_lexer.h"
#include "smt_parser.h"
#include "context.h"

#include "yices.h"
#include "yices_globals.h"
#include "yices_exit_codes.h"


static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;
static context_t context;


/*
 * Conversion of internalization code to an error message
 */
static const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error", 
  "internal error",
  "type error",
  "formula contains free variables",
  "logic not supported",
  "context does not support UF",
  "context does not support arithmetic",
  "context does not support bitvectors",
  "context does not support function equalities",
  "context does not support quantifiers",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "arithmetic solver exception",
  "bitvector solver exception",
};



/*
 * Print the translation code returned by assert_formulas
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("Assertions simplify to false\n\n"); 
    printf("unsat\n");
  } else if (code == CTX_NO_ERROR) {
    printf("Internlization OK\n\n");
    printf("unknown\n");
  } else {
    printf("unknown\n");
    code = - code;
    if (code <= NONLINEAR_NOT_SUPPORTED) {
      printf("Internalization error: %s\n\n", code2error[code]);
    } else {
      printf("%s\n\n", code2error[code]);
    }
  }
  fflush(stdout);
}





/*
 * Temporary test. Check whether one of the input assertion is reduced
 * to false by simplification. This is checked independent of the
 * logic label.
 */
static bool benchmark_reduced_to_false(smt_benchmark_t *bench) {
  uint32_t i, n;
  term_t f;

  n = bench->nformulas;
  for (i=0; i<n; i++) {
    f = bench->formulas[i];
    assert(is_boolean_term(__yices_globals.terms, f));
    if (f == false_term) {
      return true;
    }
  }

  return false;
}


/*
 * Test the context internalization functions
 */
static void test_internalization(smt_benchmark_t *bench) {
  int32_t code;

  init_context(&context, __yices_globals.terms, CTX_MODE_ONECHECK, CTX_ARCH_EGFUNSPLXBV, false);
  enable_variable_elimination(&context);
  enable_diseq_and_or_flattening(&context);
  enable_arith_elimination(&context);
  enable_bvarith_elimination(&context);

  code = assert_formulas(&context, bench->nformulas, bench->formulas);
  print_internalization_code(code);

  delete_context(&context);  
}


/*
 * Test: parse and internalize an SMT benchmark
 */
int main(int argc, char *argv[]) {
  char *filename;
  int32_t code;
  double time, mem_used;

  if (argc != 2) {
    fprintf(stderr, "Usage: %s <filename>\n", argv[0]);
    exit(YICES_EXIT_USAGE);
  }

  filename = argv[1];
  if (init_smt_file_lexer(&lexer, filename) < 0) {
    perror(filename);
    exit(YICES_EXIT_FILE_NOT_FOUND);
  }

  yices_init();
  tstack_set_smt_mode();
  init_tstack(&stack);
  init_parser(&parser, &lexer, &stack);
  init_benchmark(&bench);
  code = parse_smt_benchmark(&parser, &bench);
  if (code == 0) {
    printf("No syntax error found\n");
  } else {
    exit(YICES_EXIT_SYNTAX_ERROR);
  }

  if (benchmark_reduced_to_false(&bench)) {
    printf("Reduced to false\n\nunsat\n");
  } else {
    test_internalization(&bench);
  }
  printf("\n");
  fflush(stdout);

  time = get_cpu_time();
  mem_used = mem_size() / (1024 * 1024);
  printf("Construction time: %.4f s\n", time);
  printf("Memory used: %.2f MB\n\n", mem_used);
  fflush(stdout);


  delete_benchmark(&bench);
  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);
  yices_exit();

  return YICES_EXIT_SUCCESS;
}

