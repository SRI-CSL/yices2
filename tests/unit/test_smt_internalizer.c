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

#include "utils/cputime.h"
#include "utils/memsize.h"

#include "api/smt_logic_codes.h"
#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_parser.h"
#include "frontend/smt1/smt_term_stack.h"
#include "context/context.h"
#include "api/context_config.h"

#include "io/term_printer.h"
#include "io/type_printer.h"
#include "solvers/floyd_warshall/idl_fw_printer.h"
#include "solvers/floyd_warshall/rdl_fw_printer.h"
#include "solvers/simplex/simplex_printer.h"
#include "solvers/bv/bvsolver_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "context/context_printer.h"
#include "solvers/cdcl/gates_printer.h"

// TEMPORARY: for bv_solver_bitblast
#include "solvers/bv/bvsolver.h"

#include "utils/command_line.h"
#include "api/yices_globals.h"
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
 * - dump = whether to produce a dump file or not
 * - dump_file = name of the dump file
 *   if dump is true and dump_file is NULL, we
 *   use 'yices2intern.dmp' as default.
 * - print = whether to print the assertions (can be very expensive)
 */
static char *filename;
static char *dump_file;
static bool dump;
static bool print;

/*
 * Command-line options
 */
enum {
  dump_option,
  out_option,
  pp_option,
  help_flag,
};

#define NUM_OPTIONS 4

static option_desc_t options[NUM_OPTIONS] = {
  { "dump", 'd', FLAG_OPTION, dump_option },
  { "out",  'o', MANDATORY_STRING, out_option },
  { "print", 'p', FLAG_OPTION, pp_option },
  { "help", 'h', FLAG_OPTION, help_flag },
};

static void print_help(char *progname) {
  printf("Usage: %s [options] filename\n\n", progname);
  printf("Options:\n"
	 "  --help, -h                   Display this information\n"
	 "  --print, -p                  Pretty print the assertions (can be expensive)\n"
	 "  --dump, -d                   Dump the result\n"
	 "  --out=<file> or -o <file>    Set the dump file (default = 'yices2intern.dmp')\n"
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
  dump_file = NULL;
  dump = false;
  print = false;

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
      case dump_option:
	dump = true;
	break;

      case out_option:
	if (dump_file == NULL) {
	  dump_file = elem.s_value;
	} else {
	  fprintf(stderr, "%s: can't have several dump files\n", parser.command_name);
	  goto bad_usage;
	}
	break;

      case pp_option:
	print = true;
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
  if (filename != NULL && dump_file != NULL && strcmp(filename, dump_file) == 0) {
    fprintf(stderr, "%s: can't use '%s' for both input and dump file\n", parser.command_name, dump_file);
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
 * Print the egraph state
 */
static void dump_egraph(FILE *f, egraph_t *egraph) {
  fprintf(f, "\n--- Egraph Variables ---\n");
  print_egraph_terms(f, egraph);
  fprintf(f, "\n--- Egraph Atoms ---\n");
  print_egraph_atoms(f, egraph);
}


/*
 * Print the arithmetic solver state
 */
static void dump_idl_solver(FILE *f, idl_solver_t *idl) {
  fprintf(f, "\n--- IDL Variables ---\n");
  print_idl_var_table(f, idl);
  fprintf(f, "\n--- IDL Atoms ---\n");
  print_idl_atoms(f, idl);
  fprintf(f, "\n--- IDL Constraints ---\n");
  print_idl_axioms(f, idl);
  fprintf(f, "\n");
}

static void dump_rdl_solver(FILE *f, rdl_solver_t *rdl) {
  fprintf(f, "\n--- RDL Variables ---\n");
  print_rdl_var_table(f, rdl);
  fprintf(f, "\n--- RDL Atoms ---\n");
  print_rdl_atoms(f, rdl);
  fprintf(f, "\n--- RDL Constraints ---\n");
  print_rdl_axioms(f, rdl);
  fprintf(f, "\n");
}

static void dump_simplex_solver(FILE *f, simplex_solver_t *simplex) {
  fprintf(f, "\n--- Simplex Variables ---\n");
  print_simplex_vars(f, simplex);
  fprintf(f, "\n--- Simplex Atoms ---\n");
  print_simplex_atoms(f, simplex);
  fprintf(f, "\n--- Simplex Tableau ---\n");
  print_simplex_matrix(f, simplex);
  fprintf(f, "\n--- Simplex Bounds ---\n");
  print_simplex_bounds(f, simplex);
  fprintf(f, "\n");
}


/*
 * Print the bitvector solver state
 */
static void dump_bv_solver(FILE *f, bv_solver_t *solver) {
  fprintf(f, "\n--- Bitvector Partition ---\n");
  print_bv_solver_partition(f, solver);
  fprintf(f, "\n--- Bitvector Variables ---\n");
  print_bv_solver_vars(f, solver);
  fprintf(f, "\n--- Bitvector Atoms ---\n");
  print_bv_solver_atoms(f, solver);
  fprintf(f, "\ntotal: %"PRIu32" atoms\n", solver->atbl.natoms);
  fprintf(f, "\n--- Bitvector Bounds ---\n");
  print_bv_solver_bounds(f, solver);
  fprintf(f, "\n--- DAG ---\n");
  print_bv_solver_dag(f, solver);
  if (solver->blaster != NULL) {
    fprintf(f, "\n--- Gates ---\n");
    print_gate_table(f, &solver->blaster->htbl);
  }
  fprintf(f, "\n");
}


/*
 * Print the context:
 */
static void dump_context(FILE *f, context_t *ctx) {
  fprintf(f, "--- Substitutions ---\n");
  print_context_intern_subst(f, ctx);
  fprintf(f, "\n--- Internalization ---\n");
  print_context_intern_mapping(f, ctx);

  if (context_has_egraph(ctx)) {
    dump_egraph(f, ctx->egraph);
  }

  if (context_has_arith_solver(ctx)) {
    if (context_has_idl_solver(ctx)) {
      dump_idl_solver(f, ctx->arith_solver);
    } else if (context_has_rdl_solver(ctx)) {
      dump_rdl_solver(f, ctx->arith_solver);
    } else {
      assert(context_has_simplex_solver(ctx));
      dump_simplex_solver(f, ctx->arith_solver);
    }
  }

  if (context_has_bv_solver(ctx)) {
    dump_bv_solver(f, ctx->bv_solver);
  }

  /*
   * If arch is still AUTO_IDL or AUTO_RDL,
   * then flattening + simplification returned unsat
   * but the core is not initialized
   * so we can't print the clauses.
   */
  if (ctx->arch != CTX_ARCH_AUTO_IDL &&
      ctx->arch != CTX_ARCH_AUTO_RDL) {
    fprintf(f, "--- Clauses ---\n");
    print_clauses(f, ctx->core);
    fprintf(f, "\n");
  }


#if 0
  fprintf(f, "--- Auxiliary vectors ---\n\n");
  print_context_subst_eqs(f, ctx);
  print_context_top_eqs(f, ctx);
  print_context_top_atoms(f, ctx);
  print_context_top_formulas(f, ctx);
  print_context_top_interns(f, ctx);
  fprintf(f, "\n");
#endif

  fflush(f);
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



/*
 * Test the context internalization functions
 */
static void test_internalization(smt_benchmark_t *bench) {
  FILE *f;
  int32_t code;
  smt_logic_t logic;
  context_arch_t arch;
  bool iflag;
  bool qflag;

  /*
   * Select the architecture based on the benchmark logic
   */
  if (bench->logic_name == NULL) {
    printf("No logic specified\n\nunknown\n");
    return;
  }

  logic = smt_logic_code(bench->logic_name);
  if (logic == SMT_UNKNOWN) {
    printf("Unknown logic %s\n", bench->logic_name);
    return;
  }

  code = arch_for_logic(logic);;
  if (code < 0) {
    printf("Logic %s is not supported\n\nunknown\n", bench->logic_name);
    return;
  }

  switch (logic) {
  case QF_IDL:
    arch = CTX_ARCH_AUTO_IDL;
    iflag = false;
    qflag = false;
    break;

  case QF_RDL:
    arch = CTX_ARCH_AUTO_RDL;
    iflag = false;
    qflag = false;
    break;

  default:
    arch = (context_arch_t) code;
    iflag = iflag_for_logic(logic);
    qflag = qflag_for_logic(logic);
    break;
  }

  init_context(&context, __yices_globals.terms, logic, CTX_MODE_ONECHECK, arch, qflag);
  enable_lax_mode(&context); // FOR TESTING
  enable_variable_elimination(&context);
  enable_eq_abstraction(&context);
  enable_diseq_and_or_flattening(&context); // flatten does not help
  enable_arith_elimination(&context);
  enable_bvarith_elimination(&context);
  if (iflag) {
    enable_splx_periodic_icheck(&context);
  }

  code = assert_formulas(&context, bench->nformulas, bench->formulas);
  if (code != CTX_NO_ERROR) {
    print_internalization_code(code);
  } else if (context_is_empty(&context)) {
    printf("Reduced to the empty context\n\nsat\n");
  } else if (context_has_bv_solver(&context)) {
    // test bit-blasting
    //    if (bv_solver_compile(context.bv_solver)) {
    if (bv_solver_bitblast(context.bv_solver)) {
      printf("Bitblasting OK\n");
      print_internalization_code(code);
    } else {
      printf("Bitbasting detected inconsistency\n\nunsat\n");
    }
  } else {
    print_internalization_code(code);
  }

  if (print) {
    pp_context(stdout, &context);
  }

  if (dump) {
    if (dump_file == NULL) {
      dump_file = "yices2intern.dmp";
    }
    f = fopen(dump_file, "w");
    if (f == NULL) {
      perror(dump_file);
    } else {
      dump_context(f, &context);
      fclose(f);
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
  } else {
    exit(YICES_EXIT_SYNTAX_ERROR);
  }

  if (benchmark_reduced_to_false(&bench)) {
    printf("Reduced to false\n\nunsat\n");
  } else {
    test_internalization(&bench);
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

