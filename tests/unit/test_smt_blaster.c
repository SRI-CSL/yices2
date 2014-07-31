/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PARSE A QF_BV BENCHMARK IN SMT-LIB FORMAT THEN CONVERT IT TO CNF
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>

#include "utils/cputime.h"
#include "utils/memsize.h"

#include "api/smt_logic_codes.h"
#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_parser.h"
#include "frontend/smt1/smt_term_stack.h"
#include "context/context.h"

#include "solvers/bv/dimacs_printer.h"

// TEMPORARY: for bv_solver_bitblast
#include "solvers/bv/bvsolver.h"

#include "api/yices_globals.h"
#include "utils/command_line.h"
#include "yices.h"
#include "yices_exit_codes.h"


static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;
static context_t context;


/*
 * Parameters:
 * - filename = name of the input file (in SMT format)
 *   if filenemae is NULL, we read stdin
 * - out_file = name of the output file
 *   if out_file is NULL, we use 'yices2bblast.cnf' as default.
 */
static char *filename;
static char *out_file;


/*
 * Command-line options
 */
enum {
  out_option,
  help_flag,
};

#define NUM_OPTIONS 2

static option_desc_t options[NUM_OPTIONS] = {
  { "out",  'o', MANDATORY_STRING, out_option },
  { "help", 'h', FLAG_OPTION, help_flag },
};

static void print_help(char *progname) {
  printf("Usage: %s [options] filename\n\n", progname);
  printf("Options:\n"
	 "  --help, -h                   Display this information\n"
	 "  --out=<file> or -o <file>    Set the output file (default = 'yices2bblast.cnf')\n"
	 "\n");
  fflush(stdout);
}

static void print_usage(char *progname) {
  fprintf(stderr, "Try %s --help for more information\n", progname);
}


/*
 * Parse the command line:
 * - set filename, dump, and dump_file
 */
static void process_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;

  // default options
  filename = NULL;
  out_file = NULL;

  init_cmdline_parser(&parser, options, NUM_OPTIONS, argv, argc);
  for (;;) {
    cmdline_parse_element(&parser, &elem);
    switch (elem.status) {
    case cmdline_done:
      goto done;

    case cmdline_argument:
      if (filename == NULL) {
	filename = elem.arg;
      } else {
	fprintf(stderr, "%s: can't have several input files\n", parser.command_name);
	goto bad_usage;
      }
      break;

    case cmdline_option:
      switch (elem.key) {
      case out_option:
	if (out_file == NULL) {
	  out_file = elem.s_value;
	} else {
	  fprintf(stderr, "%s: can't have several output files\n", parser.command_name);
	  goto bad_usage;
	}
	break;

      case help_flag:
	print_help(parser.command_name);
	goto quick_exit;

      default:
	assert(false);
	break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      goto bad_usage;
    }
  }

 done:
  // check that dump_file and filename are different
  if (filename != NULL && out_file != NULL && strcmp(filename, out_file) == 0) {
    fprintf(stderr, "%s: can't use '%s' for both input and dump file\n", parser.command_name, out_file);
    goto bad_usage;
  }

  return;

 quick_exit:
  exit(YICES_EXIT_SUCCESS);

 bad_usage:
  print_usage(parser.command_name);
  exit(YICES_EXIT_USAGE);
}


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
    printf("Internalization error: %s\n\n", code2error[code]);
    printf("unknown\n");
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
 * Temporary test. Check whether the assertions are trivially true
 * after internalization and variable elimination (i.e., vectors
 * top_eqs, top_formulas, top_atoms, top_interns are all empty).
 */
static bool context_is_empty(context_t *ctx) {
  return ctx->top_eqs.size == 0 && ctx->top_atoms.size == 0 &&
    ctx->top_formulas.size == 0 && ctx->top_interns.size == 0;
}


#if 0

// NOT USED ANYMORE
/*
 * Export the clauses of core into the given file:
 * - use the DIMACs CNF format
 * - don't export the learned clauses
 * - return 0 if this works
 * - return -1 if the file can't be opened
 */
static int32_t smt_core_export(smt_core_t *core, const char *filename) {
  FILE *f;

  f = fopen(filename, "w");
  if (f == NULL) return -1;
  dimacs_print_core(f, core);
  fclose(f);

  return 0;
}

#endif

/*
 * Export the context
 */
static int32_t export_context(context_t *ctx, const char *filename) {
  FILE *f;

  f = fopen(filename, "w");
  if (f == NULL) return -1;
  dimacs_print_bvcontext(f, ctx);
  fclose(f);

  return 0;
}


/*
 * Test bitblasting
 */
static void test_blaster(smt_benchmark_t *bench) {
  int32_t code;
  smt_logic_t logic;

  /*
   * Check the benchmark logic
   */
  if (bench->logic_name == NULL) {
    printf("No logic specified\n\nunknown\n");
    return;
  }

  logic = smt_logic_code(bench->logic_name);
  assert(AUFLIA <= logic && logic <= SMT_UNKNOWN);
  if (logic != QF_BV && logic != QF_UFBV) {
    printf("Input is not a bit-vector problem (logic= %s)\n", bench->logic_name);
    return;
  }

  init_context(&context, __yices_globals.terms, logic, CTX_MODE_ONECHECK, CTX_ARCH_BV, false);
  enable_lax_mode(&context); // FOR TESTING
  enable_variable_elimination(&context);
  enable_eq_abstraction(&context);
  enable_bvarith_elimination(&context);

  code = assert_formulas(&context, bench->nformulas, bench->formulas);
  if (code != CTX_NO_ERROR) {
    print_internalization_code(code);
  } else if (context_is_empty(&context)) {
    printf("Reduced to the empty context\n\nsat\n");
  } else {
    assert(context_has_bv_solver(&context));
    // test bit-blasting
    if (bv_solver_bitblast(context.bv_solver)) {
      printf("Bitblasting OK\n");
      fflush(stdout);
      print_internalization_code(code);
      fflush(stdout);
      // one round of smt_process to handle the lemmas
      smt_process(context.core);

      if (out_file == NULL) {
	out_file = "yices2bblast.cnf";
      }
      if (export_context(&context, out_file) == 0) {
	printf("Exported to %s\n", out_file);
      } else {
	perror(out_file);
      }

    } else {
      printf("Bitbasting detected an inconsistency\n\nunsat\n");
    }

  }

  delete_context(&context);
}


/*
 * Test: parse and internalize an SMT benchmark
 */
int main(int argc, char *argv[]) {
  int32_t code;
  double time, mem_used;

  process_command_line(argc, argv);

  if (filename != NULL) {
    // read from file
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
    printf("term table: %"PRIu32" elements\n", __yices_globals.terms->nelems);
    fflush(stdout);
  } else {
    exit(YICES_EXIT_SYNTAX_ERROR);
  }

  if (benchmark_reduced_to_false(&bench)) {
    printf("Reduced to false\n\nunsat\n");
  } else {
    test_blaster(&bench);
  }
  fflush(stdout);

  time = get_cpu_time();
  mem_used = mem_size() / (1024 * 1024);
  printf("\nConstruction time: %.4f s\n", time);
  printf("Memory used: %.2f MB\n\n", mem_used);
  fflush(stdout);

  delete_benchmark(&bench);
  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);
  yices_exit();

  return YICES_EXIT_SUCCESS;
}

