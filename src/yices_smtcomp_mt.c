/*
 * Yices solver for SMT benchmarks
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <signal.h>
#include <inttypes.h>
#include <gmp.h>

#include "smt_lexer.h"
#include "smt_parser.h"
#include "smt_term_stack.h"
#include "context.h"
#include "smt_logic_codes.h"

#include "yices.h"
#include "yices_extensions.h"
#include "yices_exit_codes.h"


/*
 * GLOBAL OBJECTS
 */
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;


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
  "formula contains free variables",
  "logic not supported",
  "context does not support UF",
  "context does not support arithmetic",
  "context does not support bitvectors",
  "context does not support function equalities",
  "context does not support quantifiers",
  "context does not support lambdas",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
};




/*
 * STATISTICS DISABLED: JUST PRINT THE RESULT
 */
static void print_results(context_t *ctx) {
  smt_status_t resu;

  resu = yices_context_status(ctx);
  if (resu == STATUS_SAT) {
    printf("sat\n");
  } else if (resu == STATUS_UNSAT) {
    printf("unsat\n");
  } else {
    printf("unknown\n");
  }
  fflush(stdout);
}



/*
 * Print the translation code returned by assert
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("unsat\n");
    //    printf("Assertions simplify to false\n\n");
  } else if (code < 0) {
    printf("unknown\n");
    code = - code;
    if (code <= BVSOLVER_EXCEPTION) {
      printf("Internalization error: %s\n\n", code2error[code]);
    } else {
      printf("%s\n\n", code2error[code]);
    }
  }
  fflush(stdout);
}




/*
 * MAIN SOLVER FUNCTION
 * - parse input file (assumed to be in SMT-LIB format)
 * - solve benchmark
 * - return an exit code (defined in yices_exit_codes.h)
 */
static int process_benchmark(char *filename, bool build_model) {
  int32_t code;
  smt_logic_t logic;  // logic code read from the file
  model_t *model;
  context_t *context;
  param_t *params;

  // open input file if given or stdin
  if (filename != NULL) {
    if (init_smt_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      return YICES_EXIT_FILE_NOT_FOUND;
    }
  } else {
    init_smt_stdin_lexer(&lexer);
  }

  /*
   * Parse and build the formula
   */
  init_smt_tstack(&stack);

  init_parser(&parser, &lexer, &stack);
  init_benchmark(&bench);
  code = parse_smt_benchmark(&parser, &bench); // code < 0 means syntax error, 0 means OK

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);

  if (code < 0) {
    code = YICES_EXIT_SYNTAX_ERROR;
    goto cleanup_benchmark;
  }


  /*
   * Select architecture based on the benchmark logic
   */
  if (bench.logic_name != NULL) {
    logic = smt_logic_code(bench.logic_name);
    if (logic != QF_BV) {
      print_internalization_code(LOGIC_NOT_SUPPORTED);
      code = YICES_EXIT_ERROR;
      goto cleanup_benchmark;
    }
  } else {
    printf("unknown\n");
    printf("No logic specified\n");
    code = YICES_EXIT_ERROR;
    goto cleanup_benchmark;
  }

  /*
   * Initialize the context and set internalization options
   * and global search options
   */
  params = yices_new_param_record();
  context = yices_create_context(CTX_ARCH_BV, CTX_MODE_ONECHECK, false, false);

  /*
   * Assert and internalize
   */
  code = yices_assert_formulas(context, bench.nformulas, bench.formulas);
  if (code < 0) {
    fprintf(stderr, "Assert formulas failed: ");
    yices_print_error(stderr);
    code = YICES_EXIT_ERROR;
    goto cleanup_context;
  }

  if (code != TRIVIALLY_UNSAT) {
    code = check_context(context, params);
    if (code == STATUS_ERROR) {
      fprintf(stderr, "Check context failed: ");
      yices_print_error(stderr);
      code = YICES_EXIT_ERROR;
      goto cleanup_context;
    }
    print_results(context);

    if (build_model && (code == STATUS_SAT || code == STATUS_UNKNOWN)) {
      model = yices_get_model(context, true);
      code = yices_pp_model(stdout, model, 100, UINT32_MAX, 0);
      if (code < 0) {
	fprintf(stderr, "\nPrint model failed: ");
	yices_print_error(stderr);
      }
      yices_free_model(model);
    }
  }

  code = YICES_EXIT_SUCCESS;

  /*
   * Cleanup and return code
   */
 cleanup_context:
  yices_free_context(context);
  yices_free_param_record(params);

 cleanup_benchmark:
  delete_benchmark(&bench);

  return code;
}



int main(int argc, char *argv[]) {
  char *filename;
  int code;

  filename = NULL;
  if (argc >= 2) {
    filename = argv[1];
  } else {
    printf("Usage: %s <SMT filename> [build model]\n", argv[0]);
    exit(YICES_EXIT_USAGE);
  }

  yices_init();
  code = process_benchmark(filename, (argc==3));
  yices_exit();

  return code;
}

