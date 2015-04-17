/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>


#include "api/smt_logic_codes.h"
#include "api/yices_globals.h"
#include "context/context.h"
#include "context/context_printer.h"
#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_parser.h"
#include "frontend/smt1/smt_term_stack.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "utils/cputime.h"
#include "utils/memsize.h"

#include "yices.h"
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
  "context does not support scalar types",
  "context does not support tuples",
  "context does not support uninterpreted types",
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
 * Print the translation code returned by assert_formulas
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("Internalization OK\n");
    printf("Assertions simplify to false\n\n");
    printf("unsat\n");
  } else if (code == CTX_NO_ERROR) {
    printf("Internalization OK\n\n");
    printf("unknown\n");
  } else {
    assert(code < 0);
    code = - code;
    printf("unknown\n");
    printf("Internalization error: %s\n\n", code2error[code]);
  }

  fflush(stdout);
}



#if 0

/*
 * Print the context: not used
 */
static void dump_context(FILE *f, context_t *ctx) {
  fprintf(f, "--- Substitutions ---\n");
  print_context_intern_subst(f, ctx);
  fprintf(f, "\n--- Mapped terms ---\n\n");
  print_context_intern_mapping(f, ctx);

  fprintf(f, "--- Auxiliary vectors ---\n\n");
  print_context_subst_eqs(f, ctx);
  print_context_top_eqs(f, ctx);
  print_context_top_atoms(f, ctx);
  print_context_top_formulas(f, ctx);
  print_context_top_interns(f, ctx);

  fprintf(f, "\n");
  fflush(f);
}

#endif


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
 * Temporary test. Check whether the assertions are trivially true
 * after internalization and variable elimination (i.e., vectors
 * top_eqs, top_formulas, top_atoms, top_interns are all empty).
 */
static bool context_is_empty(context_t *ctx) {
  return ctx->top_eqs.size == 0 && ctx->top_atoms.size == 0 &&
    ctx->top_formulas.size == 0 && ctx->top_interns.size == 0;
}


/*
 * Test the context internalization functions + difference logic profiling
 */
static int32_t test_dl_profiling(smt_benchmark_t *bench) {
  dl_data_t *profile;
  smt_logic_t logic;
  context_arch_t arch;
  int32_t code;

  if (bench->logic_name != NULL) {
    logic = smt_logic_code(bench->logic_name);
    switch (logic) {
    case QF_IDL:
      arch = CTX_ARCH_AUTO_IDL;
      break;

    case QF_RDL:
      arch = CTX_ARCH_AUTO_RDL;
      break;

    default:
      print_internalization_code(LOGIC_NOT_SUPPORTED);
      return YICES_EXIT_ERROR;
    }
  } else {
    printf("No logic specified\n");
    return YICES_EXIT_ERROR;
  }

  init_context(&context, __yices_globals.terms, logic, CTX_MODE_ONECHECK, arch, false);
  enable_variable_elimination(&context);
  enable_eq_abstraction(&context);

  code = assert_formulas(&context, bench->nformulas, bench->formulas);
  if (code == CTX_NO_ERROR && context_is_empty(&context)) {
    printf("Reduced to the empty context\n\nsat\n");
  } else {
    print_internalization_code(code);
  }

  printf("term table: %"PRIu32" elements\n", context.terms->nelems);

  profile = context.dl_profile;
  if (profile != NULL) {
    printf("profile:\n");
    printf("  %"PRIu32" variables\n", profile->num_vars);
    printf("  %"PRIu32" atoms\n", profile->num_atoms);
    printf("  %"PRIu32" equalities\n", profile->num_eqs);
    printf("  sum const = ");
    q_print(stdout, &profile->sum_const);
    printf("\n");
  } else {
    printf("no profile data\n");
  }
  fflush(stdout);

  delete_context(&context);

  return 0;
}


/*
 * Test: parse and internalize an SMT benchmark
 */
int main(int argc, char *argv[]) {
  char *filename;
  int32_t code;
  double time, mem_used;

  if (argc > 2) {
    fprintf(stderr, "Usage: %s <filename>\n", argv[0]);
    exit(YICES_EXIT_USAGE);
  }

  if (argc == 2) {
    // read from file
    filename = argv[1];
    if (init_smt_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(YICES_EXIT_FILE_NOT_FOUND);
    }
  } else {
    // read from stdin
    init_smt_stdin_lexer(&lexer);
  }

  yices_init();
  init_smt_tstack(&stack);

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
    code = test_dl_profiling(&bench);
    if (code != 0) exit(code);
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

