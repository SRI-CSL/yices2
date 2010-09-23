#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>


#include "cputime.h"
#include "memsize.h"

#include "smt_lexer.h"
#include "smt_parser.h"
#include "context.h"
#include "smt_logic_codes.h"
#include "term_stack.h"

#include "term_printer.h"
#include "type_printer.h"
#include "idl_fw_printer.h"
#include "rdl_fw_printer.h"
#include "simplex_printer.h"
#include "egraph_printer.h"
#include "smt_core_printer.h"
#include "context_printer.h"

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
}

static void dump_rdl_solver(FILE *f, rdl_solver_t *rdl) {
  fprintf(f, "\n--- RDL Variables ---\n");
  print_rdl_var_table(f, rdl);
  fprintf(f, "\n--- RDL Atoms ---\n");
  print_rdl_atoms(f, rdl);
  fprintf(f, "\n--- RDL Constraints ---\n");
  print_rdl_axioms(f, rdl);
}

static void dump_simplex_solver(FILE *f, simplex_solver_t *simplex) {
  fprintf(f, "\n--- Simplex Variables ---\n");
  print_simplex_vars(f, simplex);
  fprintf(f, "\n--- Simplex Atoms ---\n");
  print_simplex_atoms(f, simplex);
  fprintf(f, "\n--- Simplex Tableau ---\n");
  print_simplex_matrix(f, simplex);
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
  bool need_icheck;
  smt_logic_t logic;
  context_arch_t arch;

  /*
   * Select the architecture based on the benchmark logic
   */
  need_icheck = false;
  arch = CTX_ARCH_NOSOLVERS;
  if (bench->logic_name != NULL) {
    logic = smt_logic_code(bench->logic_name);
    switch (logic) {
    case QF_AUFLIA:
      /*
       * Arrays + uf + simplex
       */
      arch = CTX_ARCH_EGFUNSPLX;
      break;

    case QF_AX:
      /*
       * Egraph + array solver
       */
      arch = CTX_ARCH_EGFUN;
      break;

    case QF_IDL:
      /*
       * Default for QF_IDL: automatic 
       */
      //      arch = CTX_ARCH_AUTO_IDL;
      arch = CTX_ARCH_SPLX;
      break;

    case QF_RDL:
      /*
       * Default for QF_RDL: automatic 
       */
      //      arch = CTX_ARCH_AUTO_RDL;
      arch = CTX_ARCH_SPLX;
      break;

    case QF_UF:
      /*
       * Egraph only
       */
      arch = CTX_ARCH_EG;
      break;


    case QF_LRA:
      /*
       * SIMPLEX only
       */
      arch = CTX_ARCH_SPLX;
      break;

    case QF_LIA:
      /*
       * SIMPLEX only, activate periodic integer checks
       */
      need_icheck = true;
      arch = CTX_ARCH_SPLX;
      break;

    case QF_UFIDL:
      /*
       * The default is EGRAPH + SIMPLEX.
       */
      arch = CTX_ARCH_EGSPLX;
      break;

    case QF_UFLRA:
      /*
       * EGRAPH + SIMPLEX
       */
      arch = CTX_ARCH_EGSPLX;
      break;

    case QF_UFLIA:
      /*
       * EGRAPH + SIMPLEX, activate periodic integer checks
       */
      need_icheck = true;
      arch = CTX_ARCH_EGSPLX;
      break;

    case QF_AUFBV:
      /*
       * EGRAPH + BITVECTOR + ARRAY solver
       */
      arch = CTX_ARCH_EGFUNBV;
      break;

    case QF_UFBV32:
      /*
       * EGRAPH + BITVECTOR solver
       */
      arch = CTX_ARCH_EGBV;
      break;

    case QF_BV:
      /*
       * Pure bit-vector problem
       */
      //      arch = CTX_ARCH_BV; not supported yet
      break;

    default: // use CTX_NOSOLVERS?
      break;
    }
  }

  init_context(&context, __yices_globals.terms, CTX_MODE_ONECHECK, arch, false);
  enable_variable_elimination(&context);
  enable_eq_abstraction(&context);
  enable_diseq_and_or_flattening(&context);
  enable_arith_elimination(&context);
  enable_bvarith_elimination(&context);
  if (need_icheck) {
    enable_splx_periodic_icheck(&context);
  }

  code = assert_formulas(&context, bench->nformulas, bench->formulas);
  if (code == CTX_NO_ERROR && context_is_empty(&context)) {
    printf("Reduced to the empty context\n\nsat\n");
  } else {
    print_internalization_code(code);
  }

  f = fopen("yices2intern.dmp", "w");
  if (f == NULL) {
    perror("yices2intern.dmp");
  } else {
    dump_context(f, &context);
    fclose(f);
  }

  delete_context(&context);
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
  tstack_set_smt_mode();
  init_tstack(&stack);
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
    printf("Reduced to false\n\nunsat\n\n");
  } else {
    test_internalization(&bench);
  }
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

