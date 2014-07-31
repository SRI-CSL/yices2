/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ALL SMT-LIB 2 COMMANDS
 */

#if defined(CYGWIN) || defined(MINGW)
#define EXPORTED __declspec(dllexport)
#define __YICES_DLLSPEC__ EXPORTED
#else
#define EXPORTED __attribute__((visibility("default")))
#endif


#include <stdio.h>
#include <stdarg.h>
#include <inttypes.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <errno.h>

#include "utils/refcount_strings.h"
#include "frontend/smt2/attribute_values.h"
#include "api/smt_logic_codes.h"
#include "frontend/smt2/smt2_lexer.h"
#include "frontend/smt2/smt2_commands.h"
#include "frontend/smt2/smt2_printer.h"
#include "frontend/smt2/smt2_model_printer.h"
#include "model/model_eval.h"

// for statistics
#include "solvers/funs/fun_solver.h"
#include "solvers/simplex/simplex.h"
#include "solvers/bv/bvsolver.h"
#include "solvers/floyd_warshall/idl_floyd_warshall.h"
#include "solvers/floyd_warshall/rdl_floyd_warshall.h"
#include "context/context.h"
#include "utils/cputime.h"
#include "utils/memsize.h"

// for direct context configuration
#include "api/context_config.h"

#include "yices.h"
#include "yices_exit_codes.h"
#include "api/yices_extensions.h"
#include "api/yices_globals.h"


//// PROVISIONAL

#define DUMP_CTX 0

#if DUMP_CTX

#include "term_printer.h"
#include "type_printer.h"
#include "idl_fw_printer.h"
#include "rdl_fw_printer.h"
#include "simplex_printer.h"
#include "bvsolver_printer.h"
#include "egraph_printer.h"
#include "smt_core_printer.h"
#include "context_printer.h"
#include "gates_printer.h"


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
  fprintf(f, "--- All terms ---\n");
  pp_term_table(f, ctx->terms);
  fprintf(f, "\n--- Substitutions ---\n");
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


static void dump(const char *filename, context_t *ctx) {
  FILE *f;

  f = fopen(filename, "w");
  if (f == NULL) {
    perror(filename);
  } else {
    dump_context(f, ctx);
    fclose(f);
  }
}

#endif

////



/*
 * NAME STACKS
 */

/*
 * Initialize; nothing allocated yet
 */
static void init_smt2_name_stack(smt2_name_stack_t *s) {
  s->names = NULL;
  s->top = 0;
  s->size = 0;
  s->deletions = 0;
}

/*
 * Make room for some names to be pushed
 */
static void extend_smt2_name_stack(smt2_name_stack_t *s) {
  uint32_t n;

  n = s->size;
  if (n == 0) {
    n = DEF_SMT2_NAME_STACK_SIZE;
    assert(n <= MAX_SMT2_NAME_STACK_SIZE);
    s->names = (char **) safe_malloc(n * sizeof(char *));
    s->size = n;
  } else {
    n += (n >> 1) + 1;
    if (n > MAX_SMT2_NAME_STACK_SIZE) {
      out_of_memory();
    }
    s->names = (char **) safe_realloc(s->names, n * sizeof(char *));
    s->size = n;
  }
}


/*
 * Push name on top of the stack
 * - name must be a refcount string
 * - name's reference counter is incremented
 */
static void smt2_push_name(smt2_name_stack_t *s, char *name) {
  uint32_t i;

  i = s->top;
  if (i == s->size) {
    extend_smt2_name_stack(s);
  }
  assert(i < s->size);
  s->names[i] = name;
  string_incref(name);
  s->top = i+1;
}


/*
 * Remove names on top of the stack and remove them from the term_name table
 * - ptr = new top: names[0 ... ptr-1] are kept
 */
static void smt2_pop_term_names(smt2_name_stack_t *s, uint32_t ptr) {
  char *name;
  uint32_t n;

  n = s->top;
  while (n > ptr) {
    n --;
    name = s->names[n];

    assert(yices_get_term_by_name(name) != NULL_TERM);
    yices_remove_term_name(name);
    assert(yices_get_term_by_name(name) == NULL_TERM);

    string_decref(name);
  }
  s->deletions += (s->top - ptr);
  s->top = n;
}


/*
 * Remove names on top of the stack and remove them from the type-name table
 * - ptr = new top: names[0 ... ptr - 1] are kept
 */
static void smt2_pop_type_names(smt2_name_stack_t *s, uint32_t ptr) {
  char *name;
  uint32_t n;

  n = s->top;
  while (n > ptr) {
    n --;
    name = s->names[n];

    assert(yices_get_type_by_name(name) != NULL_TYPE);
    yices_remove_type_name(name);
    assert(yices_get_type_by_name(name) == NULL_TYPE);

    string_decref(name);
  }
  s->deletions += (s->top - ptr);
  s->top = n;
}


/*
 * Remove names on top of the stack and remove them from the macro name table
 * - ptr = new top: names[0 ... ptr - 1] are kept
 *
 * NOTE: we can't delete the type_macro. We just remove the mapping
 * name -> macro id. If we remove type_constructor, then we'll delete
 * all instances of that constructor from the type table, but that's
 * not safe unless we remove all terms that have such a type.
 */
static void smt2_pop_macro_names(smt2_name_stack_t *s, uint32_t ptr) {
  char *name;
  uint32_t n;

  n = s->top;
  while (n > ptr) {
    n --;
    name = s->names[n];

    assert(yices_get_macro_by_name(name) >= 0);
    yices_remove_type_macro_name(name);
    assert(yices_get_macro_by_name(name) < 0);

    string_decref(name);
  }
  s->deletions += (s->top - ptr);
  s->top = n;
}



/*
 * Deletion
 */
static void delete_smt2_name_stack(smt2_name_stack_t *s) {
  uint32_t n;

  n = s->top;
  while (n > 0) {
    n --;
    string_decref(s->names[n]);
  }
  safe_free(s->names);
  s->names = NULL;
}


/*
 * Reset: remove all names
 */
static void reset_smt2_name_stack(smt2_name_stack_t *s) {
  delete_smt2_name_stack(s);
  assert(s->names == NULL);
  s->top = 0;
  s->size = 0;
  s->deletions = 0;
}



/*
 * NAMED-TERMS STACKS
 */

/*
 * Initialize: nothing allocated yet
 */
static void init_named_term_stack(named_term_stack_t *s) {
  s->data = NULL;
  s->top = 0;
  s->size = 0;
}


/*
 * Make room for named pairs to be added
 */
static void extend_named_term_stack(named_term_stack_t *s) {
  uint32_t n;

  n = s->size;
  if (n == 0) {
    n = DEF_NAMED_TERM_STACK_SIZE;
    assert(n <= MAX_NAMED_TERM_STACK_SIZE);
    s->data = (named_term_t *) safe_malloc(n * sizeof(named_term_t));
    s->size = n;
  } else {
    n += (n >> 1) + 1;
    if (n > MAX_NAMED_TERM_STACK_SIZE) {
      out_of_memory();
    }
    s->data = (named_term_t *) safe_realloc(s->data, n * sizeof(named_term_t));
    s->size = n;
  }
}


/*
 * Push the pair <t, name>
 * - name must be a refcount string
 * - its reference counter is incremented
 */
static void push_named_term(named_term_stack_t *s, term_t t, char *name) {
  uint32_t i;

  i = s->top;
  if (i == s->size) {
    extend_named_term_stack(s);
  }
  assert(i < s->size);
  s->data[i].term = t;
  s->data[i].name = name;
  string_incref(name);
  s->top = i+1;
}


/*
 * Remove pairs from the stack s
 * - n = new top: all pairs in s->data[0 ... n-1] are kept
 */
static void pop_named_terms(named_term_stack_t *s, uint32_t n) {
  uint32_t i;

  assert(n <= s->top);

  i = s->top;
  while (i > n) {
    i --;
    string_decref(s->data[i].name);
  }
  s->top = n;
}


/*
 * Deletion
 */
static void delete_named_term_stack(named_term_stack_t *s) {
  uint32_t i;

  i = s->top;
  while (i > 0) {
    i --;
    string_decref(s->data[i].name);
  }
  safe_free(s->data);
  s->data = NULL;
}


/*
 * Reset: remove all names then re-initialize
 */
static void reset_named_term_stack(named_term_stack_t *s) {
  delete_named_term_stack(s);
  assert(s->data == NULL);
  s->top = 0;
  s->size = 0;
}


/*
 * PUSH/POP STACK
 */

/*
 * Initialize: nothing allocated yet
 */
static void init_smt2_stack(smt2_stack_t *s) {
  s->data = NULL;
  s->top = 0;
  s->size = 0;
  s->levels = 0;
}

/*
 * Make room
 */
static void extend_smt2_stack(smt2_stack_t *s) {
  uint32_t n;

  n = s->size;
  if (n == 0) {
    n = DEF_SMT2_STACK_SIZE;
    assert(n <= MAX_SMT2_STACK_SIZE);
    s->data = (smt2_push_rec_t *) safe_malloc(n * sizeof(smt2_push_rec_t));
    s->size = n;
  } else {
    n += (n >> 1) + 1;
    if (n > MAX_SMT2_STACK_SIZE) {
      out_of_memory();
    }
    s->data = (smt2_push_rec_t *) safe_realloc(s->data, n * sizeof(smt2_push_rec_t));
    s->size = n;
  }
}


/*
 * Push data:
 * - m = multiplicity
 * - terms, types, macros = number of term/type/macro declarations
 * - named_bools. named_asserts = number of named boolean terms and assertions
 */
static void smt2_stack_push(smt2_stack_t *s, uint32_t m, uint32_t terms, uint32_t types, uint32_t macros,
			    uint32_t named_bools, uint32_t named_asserts) {
  uint32_t i;

  i = s->top;
  if (i == s->size) {
    extend_smt2_stack(s);
  }
  assert(i < s->size);
  s->data[i].multiplicity = m;
  s->data[i].term_decls = terms;
  s->data[i].type_decls = types;
  s->data[i].macro_decls = macros;
  s->data[i].named_bools = named_bools;
  s->data[i].named_asserts = named_asserts;
  s->levels += m;
  s->top = i+1;
}


/*
 * Get the top element:
 * - warning: this pointer may become invalid is data is pushed on s
 */
static inline smt2_push_rec_t *smt2_stack_top(smt2_stack_t *s) {
  assert(s->top > 0);
  return s->data + (s->top - 1);
}


static inline bool smt2_stack_is_nonempty(smt2_stack_t *s) {
  return s->top > 0;
}

/*
 * Remove the top element
 */
static void smt2_stack_pop(smt2_stack_t *s) {
  uint32_t i;

  assert(s->top > 0);
  i = s->top - 1;
  assert(s->levels >= s->data[i].multiplicity);
  s->levels -= s->data[i].multiplicity;
  s->top = i;
}

/*
 * Delete
 */
static void delete_smt2_stack(smt2_stack_t *s) {
  safe_free(s->data);
  s->data = NULL;
}


/*
 * Empty the stack
 */
static void reset_smt2_stack(smt2_stack_t *s) {
  delete_smt2_stack(s);
  assert(s->data == NULL);
  s->top = 0;
  s->size = 0;
  s->levels = 0;
}



/*
 * INTERNAL STATISTICS
 */
static void init_cmd_stats(smt2_cmd_stats_t *stats) {
  stats->num_commands = 0;
  stats->num_declare_sort = 0;
  stats->num_define_sort = 0;
  stats->num_declare_fun = 0;
  stats->num_define_fun = 0;
  stats->num_assert = 0;
  stats->num_check_sat = 0;
  stats->num_push = 0;
  stats->num_pop = 0;
  stats->num_get_value = 0;
  stats->num_get_assignment = 0;
}



/*
 * REQUIRED INFO
 */
static const char *yices_name = "Yices";
static const char *yices_authors = "Bruno Dutertre";
static const char *error_behavior = "immediate-exit";

/*
 * GLOBAL OBJECTS
 */
static bool done;    // set to true on exit
static attr_vtbl_t avtbl; // attribute values


// exported globals
smt2_globals_t __smt2_globals;

// search parameters
static param_t parameters;


/*
 * MAJOR ERRORS
 */

/*
 * If something goes wrong while writing to the output channel
 * or when closing it
 */
static void __attribute__((noreturn)) failed_output(void) {
  fprintf(stderr, "\n**************************************\n");
  fprintf(stderr, "FATAL ERROR\n");
  perror(__smt2_globals.out_name);
  fprintf(stderr, "\n**************************************\n\n");

  exit(YICES_EXIT_SYSTEM_ERROR);
}


/*
 * bug report
 */
static void __attribute__((noreturn)) report_bug(FILE *f) {
  fprintf(f, "\n*************************************************************\n");
  fprintf(f, "Please report this bug to yices-bugs@csl.sri.com.\n");
  fprintf(f, "To help us diagnose this problem, please include the\n"
                  "following information in your bug report:\n\n");
  fprintf(f, "  Yices version: %s\n", yices_version);
  fprintf(f, "  Build date: %s\n", yices_build_date);
  fprintf(f, "  Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(f, "\n");
  fprintf(f, "Thank you for your help.\n");
  fprintf(f, "*************************************************************\n\n");
  fflush(f);

  exit(YICES_EXIT_INTERNAL_ERROR);
}



/*
 * OUTPUT FUNCTIONS
 */

/*
 * Formatted output: like printf but use __smt2_globals.out
 */
static void print_out(const char *format, ...) {
  va_list p;

  va_start(p, format);
  if (vfprintf(__smt2_globals.out, format, p) < 0) {
    failed_output();
  }
  va_end(p);
}


/*
 * Flush the output channel
 */
static inline void flush_out(void) {
  if (fflush(__smt2_globals.out) == EOF) {
    failed_output();
  }
}


/*
 * Report success
 */
static void report_success(void) {
  if (__smt2_globals.print_success) {
    print_out("success\n");
    flush_out();
  }
}




/*
 * ERROR REPORTS
 */

/*
 * Error prefix/suffix
 * - SMT2 wants errors to be printed as
 *        (error "explanation")
 *   on the current output channel
 * - start_error(l, c) prints '(error "at line x, column y: '
 * - open_error() prints '(error "
 * - close_error() prints '")' and a newline then flush the output channel
 */
static void start_error(uint32_t line, uint32_t column) {
  print_out("(error \"at line %"PRIu32", column %"PRIu32": ", line, column);
}

static void open_error(void) {
  print_out("(error \"");
}

static void close_error(void) {
  print_out("\")\n");
  flush_out();
}


/*
 * Formatted error: like printf but add the prefix and close
 */
static void print_error(const char *format, ...) {
  va_list p;

  open_error();
  va_start(p, format);
  if (vfprintf(__smt2_globals.out, format, p) < 0) {
    failed_output();
  }
  va_end(p);
  close_error();
}


/*
 * Syntax error (reported by tstack)
 * - lex = lexer
 * - expected_token = either an smt2_token or -1
 *
 * lex is as follows:
 * - current_token(lex) = token that caused the error
 * - current_token_value(lex) = corresponding string
 * - current_token_length(lex) = length of that string
 * - lex->tk_line and lex->tk_column = start of the token in the input
 * - lex->reader.name  = name of the input file (NULL means input is stdin)
 */
static inline char *tkval(lexer_t *lex) {
  return current_token_value(lex);
}

void smt2_syntax_error(lexer_t *lex, int32_t expected_token) {
  reader_t *rd;
  smt2_token_t tk;

  tk = current_token(lex);
  rd = &lex->reader;

  start_error(rd->line, rd->column);

  switch (tk) {
  case SMT2_TK_INVALID_STRING:
    print_out("missing string terminator");
    break;

  case SMT2_TK_INVALID_NUMERAL:
    print_out("invalid numeral %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_DECIMAL:
    print_out("invalid decimal %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_HEXADECIMAL:
    print_out("invalid hexadecimal constant %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_BINARY:
    print_out("invalid binary constant %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_SYMBOL:
    print_out("invalid symbol");
    break;

  case SMT2_TK_INVALID_KEYWORD:
    print_out("invalid keyword");
    break;

  case SMT2_TK_ERROR:
    print_out("invalid token %s", tkval(lex));
    break;

  default:
    if (expected_token >= 0) {
      print_out("syntax error: %s expected", smt2_token_to_string(expected_token));
    } else if (expected_token == -2 && tk == SMT2_TK_SYMBOL) {
      print_out("syntax error: %s is not a command", tkval(lex));
    } else {
      print_out("syntax error");
    }
    break;
  }

  close_error();
}


/*
 * ERROR FROM YICES (in yices_error_report)
 */

// mismatch between logic and assertions
static void unsupported_construct(const char *what) {
  if (__smt2_globals.logic_name != NULL) {
    print_out("%s not allowed in logic %s", what, __smt2_globals.logic_name);
  } else {
    print_out("%s not supported");
  }
}

/*
 * If full is true: print (error <message>)
 * Otherwise: print <message>
 */
static void print_yices_error(bool full) {
  error_report_t *error;

  if (full) open_error();

  error = yices_error_report();
  switch (error->code) {
  case INVALID_BITSHIFT:
    print_out("invalid index in rotate");
    break;
  case INVALID_BVEXTRACT:
    print_out("invalid indices in bit-vector extract");
    break;
  case TOO_MANY_ARGUMENTS:
    print_out("too many arguments. Function arity is at most %"PRIu32, YICES_MAX_ARITY);
    break;
  case TOO_MANY_VARS:
    print_out("too many variables in quantifier. Max is %"PRIu32, YICES_MAX_VARS);
    break;
  case MAX_BVSIZE_EXCEEDED:
    print_out("bit-vector size too large. Max is %"PRIu32, YICES_MAX_BVSIZE);
    break;
  case DEGREE_OVERFLOW:
    print_out("maximal polynomial degree exceeded");
    break;
  case DIVISION_BY_ZERO:
    print_out("division by zero");
    break;
  case POS_INT_REQUIRED:
    print_out("integer argument must be positive");
    break;
  case NONNEG_INT_REQUIRED:
    print_out("integer argument must be non-negative");
    break;
  case FUNCTION_REQUIRED:
    print_out("argument is not a function");
    break;
  case ARITHTERM_REQUIRED:
    print_out("argument is not an arithmetic term");
    break;
  case BITVECTOR_REQUIRED:
    print_out("argument is not a bit-vector term");
    break;
  case WRONG_NUMBER_OF_ARGUMENTS:
    print_out("wrong number of arguments");
    break;
  case TYPE_MISMATCH:
    print_out("type error");
    break;
  case INCOMPATIBLE_TYPES:
    print_out("incompatible types");
    break;
  case INCOMPATIBLE_BVSIZES:
    print_out("arguments do not have the same number of bits");
    break;
  case EMPTY_BITVECTOR:
    print_out("bit-vectors can't have 0 bits");
    break;
  case ARITHCONSTANT_REQUIRED:
    print_out("argument is not an arithmetic constant");
    break;
  case TOO_MANY_MACRO_PARAMS:
    print_out("too many arguments in sort constructor. Max is %"PRIu32, TYPE_MACRO_MAX_ARITY);
    break;

  case CTX_FREE_VAR_IN_FORMULA:
    print_out("formula contains free variable");
    break;

  case CTX_LOGIC_NOT_SUPPORTED:
    print_out("logic not supported");
    break;

  case CTX_UF_NOT_SUPPORTED:
    unsupported_construct("UF is");
    break;

  case CTX_ARITH_NOT_SUPPORTED:
    unsupported_construct("arithmetic is");
    break;

  case CTX_BV_NOT_SUPPORTED:
    unsupported_construct("bitvectors are");
    break;

  case CTX_ARRAYS_NOT_SUPPORTED:
    unsupported_construct("arrays are");
    break;

  case CTX_QUANTIFIERS_NOT_SUPPORTED:
    unsupported_construct("quantifiers are");
    break;

  case CTX_NONLINEAR_ARITH_NOT_SUPPORTED:
    unsupported_construct("non-linear arithmetic is");
    break;

  case CTX_FORMULA_NOT_IDL:
    print_out("formula is not in integer difference logic");
    break;

  case CTX_FORMULA_NOT_RDL:
    print_out("formula is not in real difference logic");
    break;

  case CTX_TOO_MANY_ARITH_VARS:
    print_out("too many variables for the arithemtic solver");
    break;

  case CTX_TOO_MANY_ARITH_ATOMS:
    print_out("too many atoms for the arithmetic solver");
    break;

  case CTX_TOO_MANY_BV_VARS:
    print_out("too many variables for the bit-vector solver");
    break;

  case CTX_TOO_MANY_BV_ATOMS:
    print_out("too many atoms for the bit-vector solver");
    break;

  case CTX_ARITH_SOLVER_EXCEPTION:
  case CTX_BV_SOLVER_EXCEPTION:
  case CTX_ARRAY_SOLVER_EXCEPTION:
  case CTX_OPERATION_NOT_SUPPORTED:
  case CTX_INVALID_CONFIG:
  case CTX_UNKNOWN_PARAMETER:
  case CTX_INVALID_PARAMETER_VALUE:
  case CTX_UNKNOWN_LOGIC:
    print_out("context exception");
    break;

  case EVAL_QUANTIFIER:
    print_out("can't evaluate quantified terms");
    break;

  case EVAL_LAMBDA:
    print_out("can't evaluate lambda terms");
    break;

  case EVAL_UNKNOWN_TERM:
  case EVAL_FREEVAR_IN_TERM:
  case EVAL_OVERFLOW:
  case EVAL_FAILED:
    print_out("can't evaluate term value");
    break;

  case OUTPUT_ERROR:
    print_out(" IO error");
    break;

  default:
    print_out("BUG detected");
    if (full) close_error();
    report_bug(__smt2_globals.err);
    break;
  }

  if (full) close_error();
}



/*
 * EXCEPTIONS
 */

/*
 * Error messages for tstack exceptions
 * NULL means that this should never occur (i.e., fatal exception)
 */
static const char * const exception_string[NUM_SMT2_EXCEPTIONS] = {
  NULL,                                 // TSTACK_NO_ERROR
  NULL,                                 // TSTACK_INTERNAL_ERROR
  "operation not implemented",          // TSTACK_OP_NOT_IMPLEMENTED
  "undefined term",                     // TSTACK_UNDEF_TERM
  "undefined sort",                     // TSTACK_UNDEF_TYPE
  "undefined sort constructor",         // TSTACK_UNDEF_MACRO,
  "invalid numeral",                    // TSTACK_RATIONAL_FORMAT
  "invalid decimal'",                   // TSTACK_FLOAT_FORMAT
  "invalid binary",                     // TSTACK_BVBIN_FORMAT
  "invalid hexadecimal",                // TSTACK_BVHEX_FORMAT
  "can't redefine sort",                // TSTACK_TYPENAME_REDEF
  "can't redefine term",                // TSTACK_TERMNAME_REDEF
  "can't redefine sort constructor",    // TSTACK_MACRO_REDEF
  NULL,                                 // TSTACK_DUPLICATE_SCALAR_NAME
  "duplicate variable name",            // TSTACK_DUPLICATE_VAR_NAME
  "duplicate variable name",            // TSTACK_DUPLICATE_TYPE_VAR_NAME
  NULL,                                 // TSTACK_INVALID_OP
  "wrong number of arguments",          // TSTACK_INVALID_FRAME
  "constant too large",                 // TSTACK_INTEGER_OVERFLOW
  NULL,                                 // TSTACK_NEGATIVE_EXPONENT
  "integer required",                   // TSTACK_NOT_AN_INTEGER
  "string required",                    // TSTACK_NOT_A_STRING
  "symbol required",                    // TSTACK_NOT_A_SYMBOL
  "numeral required",                   // TSTACK_NOT_A_RATIONAL
  "sort required",                      // TSTACK_NOT_A_TYPE
  "error in arithmetic operation",      // TSTACK_ARITH_ERROR
  "division by zero",                   // TSTACK_DIVIDE_BY_ZERO
  "divisor must be constant",           // TSTACK_NON_CONSTANT_DIVISOR
  "size must be positive",              // TSTACK_NONPOSITIVE_BVSIZE
  "bitvectors have incompatible sizes", // TSTACK_INCOMPATIBLE_BVSIZES
  "number can't be converted to a bitvector constant", // TSTACK_INVALID_BVCONSTANT
  "error in bitvector arithmetic operation",  //TSTACK_BVARITH_ERROR
  "error in bitvector operation",       // TSTACK_BVLOGIC_ERROR
  "incompatible sort in definition",    // TSTACK_TYPE_ERROR_IN_DEFTERM
  "invalid term",                       // TSTACK_STRINGS_ARE_NOT_TERMS
  NULL,                                 // TSTACK_YICES_ERROR
  "missing symbol in :named attribute", // SMT2_MISSING_NAME
  "no pattern given",                   // SMT2_MISSING_PATTERN
  "not a sort identifier",              // SMT2_SYMBOL_NOT_SORT
  "not an indexed sort identifier",     // SMT2_SYMBOL_NOT_IDX_SORT
  "not a sort constructor",             // SMT2_SYMBOL_NOT_SORT_OP
  "not an indexed sort constructor",    // SMT2_SYMBOL_NOT_IDX_SORT_OP
  "not a term identifier",              // SMT2_SYMBOL_NOT_TERM
  "not an indexed term identifier",     // SMT2_SYMBOL_NOT_IDX_TERM
  "not a function identifier",          // SMT2_SYMBOL_NOT_FUNCTION
  "not an indexed function identifier", // SMT2_SYMBOL_NOT_IDX_FUNCTION
  "undefined identifier",               // SMT2_UNDEF_IDX_SORT
  "undefined identifier",               // SMT2_UNDEF_IDX_SORT_OP
  "undefined identifier",               // SMT2_UNDEF_IDX_TERM
  "undefined identifier",               // SMT2_UNDEF_IDX_FUNCTION
  "invalid qualifier: types don't match",  // SMT2_TYPE_ERROR_IN_QUAL
  "sort qualifier not supported",       // SMT2_QUAL_NOT_IMPLEMENTED
  "invalid bitvector constant",         // SMT2_INVALID_IDX_BV
  "invalid :named attribute (term is not ground)",    // SMT2_NAMED_TERM_NOT_GROUND
  "invalid :named attribute (name is already used)",  // SMT2_NAMED_SYMBOL_REUSED
  NULL,                                 // SMT2_SYMBOL_REDEF_SORT
  NULL,                                 // SMT2_SYMBOL_REDEF_FUN
};


/*
 * Conversion of opcodes to strings
 */
static const char * const opcode_string[NUM_SMT2_OPCODES] = {
  NULL,                   // NO_OP
  "sort definition",      // DEFINE_TYPE (should not occur?)
  "term definition",      // DEFINE_TERM (should not occur?)
  "binding",              // BIND?
  "variable declaration", // DECLARE_VAR
  "sort-variable declaration", // DECLARE_TYPE_VAR
  "let",                  // LET
  "BitVec",               // MK_BV_TYPE
  NULL,                   // MK_SCALAR_TYPE
  NULL,                   // MK_TUPLE_TYPE
  "function type",        // MK_FUN_TYPE
  "type constructor",     // MK_APP_TYPE
  "function application", // MK_APPLY
  "ite",                  // MK_ITE
  "equality",             // MK_EQ
  "disequality",          // MK_DISEQ
  "distinct",             // MK_DISTINCT
  "not",                  // MK_NOT
  "or",                   // MK_OR
  "and",                  // MK_AND
  "xor",                  // MK_XOR
  "iff",                  // MK_IFF (not in SMT2?)
  "=>",                   // MK_IMPLIES
  NULL,                   // MK_TUPLE
  NULL,                   // MK_SELECT
  NULL,                   // MK_TUPLE_UPDATE
  NULL,                   // MK_UPDATE (replaced by SMT2_MK_STORE)
  "forall",               // MK_FORALL
  "exists",               // MK_EXISTS
  "lambda",               // MK_LAMBDA (not in SMT2)
  "addition",             // MK_ADD
  "subtraction",          // MK_SUB
  "negation",             // MK_NEG
  "multiplication",       // MK_MUL
  "division",             // MK_DIVISION
  "exponentiation",       // MK_POW
  "inequality",           // MK_GE
  "inequality",           // MK_GT
  "inequality",           // MK_LE
  "inequality",           // MK_LT
  "bitvector constant",   // MK_BV_CONST
  "bvadd",                // MK_BV_ADD
  "bvsub",                // MK_BV_SUB
  "bvmul",                // MK_BV_MUL
  "bvneg",                // MK_BV_NEG
  "bvpow",                // MK_BV_POW (not in SMT2)
  "bvudiv",               // MK_BV_DIV
  "bvurem",               // MK_BV_REM
  "bvsdiv",               // MK_BV_SDIV
  "bvurem",               // MK_BV_SREM
  "bvsmod",               // MK_BV_SMOD
  "bvnot",                // MK_BV_NOT
  "bvand",                // MK_BV_AND
  "bvor",                 // MK_BV_OR
  "bvxor",                // MK_BV_XOR
  "bvnand",               // MK_BV_NAND
  "bvnor",                // MK_BV_NOR
  "bvxnor",               // MK_BV_XNOR
  NULL,                   // MK_BV_SHIFT_LEFT0
  NULL,                   // MK_BV_SHIFT_LEFT1
  NULL,                   // MK_BV_SHIFT_RIGHT0
  NULL,                   // MK_BV_SHIFT_RIGHT1
  NULL,                   // MK_BV_ASHIFT_RIGHT
  "rotate_left",          // MK_BV_ROTATE_LEFT
  "rotate_right",         // MK_BV_ROTATE_RIGHT
  "bvshl",                // MK_BV_SHL
  "bvlshr",               // MK_BV_LSHR
  "bvashr",               // MK_BV_ASHR
  "extract",              // MK_BV_EXTRACT
  "concat",               // MK_BV_CONCAT
  "repeat",               // MK_BV_REPEAT
  "sign_extend",          // MK_BV_SIGN_EXTEND
  "zero_extend",          // MK_BV_ZERO_EXTEND
  "bvredand",             // MK_BV_REDAND (not in SMT2)
  "bvredor",              // MK_BV_REDOR (not in SMT2)
  "bvcomp",               // MK_BV_COMP
  "bvuge",                // MK_BV_GE,
  "bvugt",                // MK_BV_GT
  "bvule",                // MK_BV_LE
  "bvult",                // MK_BV_LT
  "bvsge",                // MK_BV_SGE
  "bvsgt",                // MK_BV_SGT
  "bvsle",                // MK_BV_SLE
  "bvslt",                // MK_BV_SLT
  "build term",           // BUILD_TERM
  "build_type",           // BUILD_TYPE
  //
  "exit",                 // SMT2_EXIT
  "end of file",          // SMT2_SILENT_EXIT
  "get-assertions",       // SMT2_GET_ASSERTIONS
  "get-assignment",       // SMT2_GET_ASSIGNMENT
  "get-proof",            // SMT2_GET_PROOF
  "get-unsat-core",       // SMT2_GET_UNSAT_CORE
  "get-value",            // SMT2_GET_VALUE
  "get-option",           // SMT2_GET_OPTION
  "get-info",             // SMT2_GET_INFO
  "set-option",           // SMT2_SET_OPTION
  "set-info",             // SMT2_SET_INFO
  "set-logic",            // SMT2_SET_LOGIC
  "push",                 // SMT2_PUSH
  "pop",                  // SMT2_POP
  "assert",               // SMT2_ASSERT,
  "check-sat",            // SMT2_CHECK_SAT,
  "declare-sort",         // SMT2_DECLARE_SORT
  "define-sort",          // SMT2_DEFINE_SORT
  "declare-fun",          // SMT2_DECLARE_FUN
  "define-fun",           // SMT2_DEFINE_FUN
  "get-model",            // SMT2_GET_MODEL (not standard)
  "echo",                 // SMT2_ECHO      (not standard)
  "reset",                // SMT2_RESET     (not standard)
  //
  "attributes",           // SMT2_MAKE_ATTR_LIST
  "term annotation",      // SMT2_ADD_ATTRIBUTES
  "Array",                // SMT2_MK_ARRAY
  "select",               // SMT2_MK_SELECT
  "store",                // SMT2_MK_STORE
  "indexed_sort",         // SMT2_INDEXED_SORT
  "sort expression",      // SMT2_APP_INDEXED_SORT
  "indexed identifier",   // SMT2_INDEXED_TERM
  "sort qualifier",       // SMT2_SORTED_TERM
  "sort qualifier",       // SMT2_SORTED_INDEXED_TERM
  "function application", // SMT2_INDEXED_APPLY
  "sort qualifier",       // SMT2_SORTED_APPLY
  "sort qualifier",       // SMT2_SORTED_INDEXED_APPLY
  // operations not supported
  "div",                  // SMT2_MK_DIV
  "mod",                  // SMT2_MK_MOD
  "abs",                  // SMT2_MK_ABS
  "to_real",              // SMT2_MK_TO_REAL
  "to_int",               // SMT2_MK_TO_INT
  "is_int",               // SMT2_MK_IS_INT
  "divisible",            // SMT2_MK_DIVISIBLE
};


/*
 * Check whether a symbol should be printed with quotes | .. |
 */
static bool symbol_needs_quotes(const char *s) {
  int c;

  c = *s++;
  if (c == '\0') {
    return true; // empty symbol
  }

  do {
    if (isspace(c)) {
      return true;
    }
    c = *s ++;
  } while (c != '\0');

  return false;
}


/*
 * Exception raised by tstack
 * - tstack = term stack
 * - exception = error code (defined in term_stack2.h)
 *
 * Error location in the input file is given by
 * - tstack->error_loc.line
 * - tstack->error_loc.column
 *
 * Extra fields (depending on the exception)
 * - tstack->error_string = erroneous input
 * - tstack->error_op = erroneous operation
 */
void smt2_tstack_error(tstack_t *tstack, int32_t exception) {
  start_error(tstack->error_loc.line, tstack->error_loc.column);

  switch (exception) {
  case TSTACK_OP_NOT_IMPLEMENTED:
    print_out("operation %s not implemented", opcode_string[tstack->error_op]);
    break;

  case TSTACK_UNDEF_TERM:
  case TSTACK_UNDEF_TYPE:
  case TSTACK_UNDEF_MACRO:
  case TSTACK_DUPLICATE_VAR_NAME:
  case TSTACK_DUPLICATE_TYPE_VAR_NAME:
  case TSTACK_TYPENAME_REDEF:
  case TSTACK_TERMNAME_REDEF:
  case TSTACK_MACRO_REDEF:
  case SMT2_SYMBOL_NOT_SORT:
  case SMT2_SYMBOL_NOT_IDX_SORT:
  case SMT2_SYMBOL_NOT_SORT_OP:
  case SMT2_SYMBOL_NOT_IDX_SORT_OP:
  case SMT2_SYMBOL_NOT_TERM:
  case SMT2_SYMBOL_NOT_IDX_TERM:
  case SMT2_SYMBOL_NOT_FUNCTION:
  case SMT2_SYMBOL_NOT_IDX_FUNCTION:
  case SMT2_UNDEF_IDX_SORT:
  case SMT2_UNDEF_IDX_SORT_OP:
  case SMT2_UNDEF_IDX_TERM:
  case SMT2_UNDEF_IDX_FUNCTION:
    if (symbol_needs_quotes(tstack->error_string)) {
      print_out("%s: |%s|", exception_string[exception], tstack->error_string);
    } else {
      print_out("%s: %s", exception_string[exception], tstack->error_string);
    }
    break;

  case SMT2_SYMBOL_REDEF_SORT:
  case SMT2_SYMBOL_REDEF_FUN:
    if (symbol_needs_quotes(tstack->error_string)) {
      print_out("name |%s| is already defined in the logic", tstack->error_string);
    } else {
      print_out("name %s is already defined in the logic", tstack->error_string);
    }
    break;


  case TSTACK_RATIONAL_FORMAT:
  case TSTACK_FLOAT_FORMAT:
  case TSTACK_BVBIN_FORMAT:
  case TSTACK_BVHEX_FORMAT:
    print_out("%s: %s", exception_string[exception], tstack->error_string);
    break;

  case TSTACK_INVALID_FRAME:
  case TSTACK_NONPOSITIVE_BVSIZE:
    print_out("%s in %s", exception_string[exception], opcode_string[tstack->error_op]);
    break;

  case TSTACK_INTEGER_OVERFLOW:
  case TSTACK_NOT_AN_INTEGER:
  case TSTACK_NOT_A_STRING:
  case TSTACK_NOT_A_SYMBOL:
  case TSTACK_NOT_A_RATIONAL:
  case TSTACK_NOT_A_TYPE:
  case TSTACK_ARITH_ERROR:
  case TSTACK_DIVIDE_BY_ZERO:
  case TSTACK_NON_CONSTANT_DIVISOR:
  case TSTACK_INCOMPATIBLE_BVSIZES:
  case TSTACK_INVALID_BVCONSTANT:
  case TSTACK_BVARITH_ERROR:
  case TSTACK_BVLOGIC_ERROR:
  case TSTACK_TYPE_ERROR_IN_DEFTERM:
  case SMT2_MISSING_NAME:
  case SMT2_MISSING_PATTERN:
  case SMT2_TYPE_ERROR_IN_QUAL:
  case SMT2_QUAL_NOT_IMPLEMENTED:
    print_out("%s", exception_string[exception]);
    break;

  case TSTACK_STRINGS_ARE_NOT_TERMS:
    print_out("%s: \"%s\"", exception_string[exception], tstack->error_string);
    break;

  case TSTACK_YICES_ERROR:
    // TODO: extract mode information from yices_error_report();
    print_out("in %s: ", opcode_string[tstack->error_op]);
    print_yices_error(false);
    break;

  case SMT2_INVALID_IDX_BV:
  case SMT2_NAMED_TERM_NOT_GROUND:
  case SMT2_NAMED_SYMBOL_REUSED:
    print_out("%s", exception_string[exception]);
    break;

  case TSTACK_NO_ERROR:
  case TSTACK_INTERNAL_ERROR:
  case TSTACK_DUPLICATE_SCALAR_NAME:
  case TSTACK_INVALID_OP:
  case TSTACK_NEGATIVE_EXPONENT:
  default:
    print_out("FATAL ERROR");
    close_error();
    report_bug(__smt2_globals.err);
    break;
  }

  close_error();
}



/*
 * Bug report: unexpected status
 */
static void __attribute__((noreturn)) bad_status_bug(FILE *f) {
  print_error("Internal error: unexpected context status");
  flush_out();
  report_bug(f);
}



/*
 * PRINT STATUS AND STATISTICS
 */
static const char * const status2string[] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  "error",
};

static void show_status(smt_status_t status) {
  print_out("%s\n", status2string[status]);
}


/*
 * Statistics about each solvers
 */
static void show_core_stats(smt_core_t *core) {
  print_out(" :boolean-variables %"PRIu32"\n", num_vars(core));
  print_out(" :atoms %"PRIu32"\n", num_atoms(core));
  print_out(" :clauses %"PRIu32"\n", num_clauses(core));
  print_out(" :restarts %"PRIu32"\n", num_restarts(core));
  print_out(" :clause-db-reduce %"PRIu32"\n", num_reduce_calls(core));
  print_out(" :clause-db-simplify %"PRIu32"\n", num_simplify_calls(core));
  print_out(" :decisions %"PRIu64"\n", num_decisions(core));
  print_out(" :conflicts %"PRIu64"\n", num_conflicts(core));
  print_out(" :theory-conflicts %"PRIu32"\n", num_theory_conflicts(core));
  print_out(" :boolean-propagations %"PRIu64"\n", num_propagations(core));
  print_out(" :theory-propagations %"PRIu32"\n", num_theory_propagations(core));
}

static void show_egraph_stats(egraph_t *egraph) {
  print_out(" :egraph-terms %"PRIu32"\n", egraph_num_terms(egraph));
  print_out(" :egraph-atoms %"PRIu32"\n", egraph_num_atoms(egraph));
  print_out(" :egraph-conflicts %"PRIu32"\n", egraph_num_conflicts(egraph));
  print_out(" :egraph-ackermann-lemmas %"PRIu32"\n", egraph_all_ackermann(egraph));
  print_out(" :egraph-final-checks %"PRIu32"\n", egraph_num_final_checks(egraph));
  print_out(" :egraph-interface-lemmas %"PRIu32"\n", egraph_num_interface_eqs(egraph));
}

static void show_funsolver_stats(fun_solver_t *solver) {
  print_out(" :array-vars %"PRIu32"\n", fun_solver_num_vars(solver));
  print_out(" :array-edges %"PRIu32"\n", fun_solver_num_edges(solver));
  print_out(" :array-update1-axioms %"PRIu32"\n", fun_solver_num_update1_axioms(solver));
  print_out(" :array-update2-axioms %"PRIu32"\n", fun_solver_num_update2_axioms(solver));
  print_out(" :array-extensionality-axioms %"PRIu32"\n", fun_solver_num_extensionality_axioms(solver));
}

static void show_simplex_stats(simplex_solver_t *solver) {
  simplex_collect_statistics(solver);
  print_out(" :simplex-vars %"PRIu32"\n", simplex_num_vars(solver));
  print_out(" :simplex-rows %"PRIu32"\n", simplex_num_rows(solver));
  print_out(" :simplex-atoms %"PRIu32"\n", simplex_num_atoms(solver));
  print_out(" :simplex-pivots %"PRIu32"\n", simplex_num_pivots(solver));
  print_out(" :simplex-conflicts %"PRIu32"\n", simplex_num_conflicts(solver));
  print_out(" :simplex-interface-lemmas %"PRIu32"\n", simplex_num_interface_lemmas(solver));
  if (simplex_num_make_integer_feasible(solver) > 0 ||
      simplex_num_dioph_checks(solver) > 0) {
    print_out(" :simplex-integer-vars %"PRIu32"\n", simplex_num_integer_vars(solver));
    print_out(" :simplex-branch-and-bound %"PRIu32"\n", simplex_num_branch_and_bound(solver));
    print_out(" :simplex-gcd-conflicts %"PRIu32"\n", simplex_num_gcd_conflicts(solver));
    print_out(" :simplex-diophantine-conflicts %"PRIu32"\n", simplex_num_dioph_conflicts(solver));
  }
}

static void show_bvsolver_stats(bv_solver_t *solver) {
  print_out(" :bvsolver-vars %"PRIu32"\n", bv_solver_num_vars(solver));
  print_out(" :bvsolver-atoms %"PRIu32"\n", bv_solver_num_atoms(solver));
  print_out(" :bvsolver-equiv-lemmas %"PRIu32"\n", bv_solver_equiv_lemmas(solver));
  print_out(" :bvsolver-interface-lemmas %"PRIu32"\n", bv_solver_interface_lemmas(solver));
}

static void show_idl_fw_stats(idl_solver_t *solver) {
  print_out(" :idl-solver-vars %"PRIu32"\n", idl_num_vars(solver));
  print_out(" :idl-solver-atoms %"PRIu32"\n", idl_num_atoms(solver));
}

static void show_rdl_fw_stats(rdl_solver_t *solver) {
  print_out(" :rdl-solver-vars %"PRIu32"\n", rdl_num_vars(solver));
  print_out(" :rdl-solver-atoms %"PRIu32"\n", rdl_num_atoms(solver));
}


/*
 * Context statistics
 */
static void show_ctx_stats(context_t *ctx) {
  assert(ctx->core != NULL);
  show_core_stats(ctx->core);

  if (context_has_egraph(ctx)) {
    show_egraph_stats(ctx->egraph);
  }

  if (context_has_fun_solver(ctx)) {
    show_funsolver_stats(ctx->fun_solver);
  }
  if (context_has_arith_solver(ctx)) {
    if (context_has_simplex_solver(ctx)) {
      show_simplex_stats(ctx->arith_solver);
    } else if (context_has_idl_solver(ctx)) {
      show_idl_fw_stats(ctx->arith_solver);
    } else {
      assert(context_has_rdl_solver(ctx));
      show_rdl_fw_stats(ctx->arith_solver);
    }
  }

  if (context_has_bv_solver(ctx)) {
    show_bvsolver_stats(ctx->bv_solver);
  }
}


/*
 * Global state
 */
static void show_statistics(smt2_globals_t *g) {
  double time, mem;

  time = get_cpu_time();
  mem = mem_size() / (1024*1024);

  print_out("(:num-terms %"PRIu32"\n", yices_num_terms());
  print_out(" :num-types %"PRIu32"\n", yices_num_types());
  print_out(" :total-run-time %.3f\n", time);
  if (mem > 0) {
    print_out(" :mem-usage %.3f\n", mem);
  }
  if (g->ctx != NULL) {
    show_ctx_stats(g->ctx);
  }
  print_out(")\n");
  flush_out();
}


/*
 * OUTPUT/ERROR FILES
 */

/*
 * Close the output file and delete its name
 */
static void close_output_file(smt2_globals_t *g) {
  if (g->out != stdout) {
    assert(g->out_name != NULL);
    if (fclose(g->out) == EOF) {
      failed_output();
    }
    string_decref(g->out_name);
    g->out_name = NULL;
  }
  assert(g->out_name == NULL);
}

/*
 * Same thing for the error file
 */
static void close_error_file(smt2_globals_t *g) {
  if (g->err != stderr) {
    assert(g->err_name != NULL);
    if (fclose(g->err) == EOF) {
      failed_output();
    }
    string_decref(g->err_name);
    g->err_name = NULL;
  }
  assert(g->err_name == NULL);;
}



/*
 * Allocate and initialize the trace object
 */
static tracer_t *get_tracer(smt2_globals_t *g) {
  tracer_t *tmp;

  tmp = g->tracer;
  if (tmp == NULL) {
    tmp = (tracer_t *) safe_malloc(sizeof(tracer_t));
    init_trace(tmp);
    set_trace_vlevel(tmp, g->verbosity);
    set_trace_file(tmp, g->err);
    g->tracer = tmp;
  }
  return tmp;
}


/*
 * Delete the trace object
 */
static void delete_tracer(smt2_globals_t *g) {
  if (g->tracer != NULL) {
    delete_trace(g->tracer);
    safe_free(g->tracer);
    g->tracer = NULL;
  }
}

/*
 * Change the trace file
 */
static void update_trace_file(smt2_globals_t *g) {
  if (g->tracer != NULL) {
    set_trace_file(g->tracer, g->err);
  }
}


/*
 * Change the verbosity level in g->tracer
 * - create the tracer if needed
 */
static void update_trace_verbosity(smt2_globals_t *g) {
  tracer_t *tmp;

  if (g->tracer != NULL) {
    set_trace_vlevel(g->tracer, g->verbosity);
  } else if (g->verbosity > 0) {
    tmp = get_tracer(g);
    if (g->ctx != NULL) context_set_trace(g->ctx, tmp);
  }
}


/*
 * Initialize pretty printer object to use the output channel
 */
static void init_pretty_printer(yices_pp_t *printer, smt2_globals_t *g) {
  init_yices_pp(printer, g->out, &g->pp_area, PP_VMODE, 0);
}


/*
 * INFO TABLE
 */

/*
 * Return the table (construct and initialize it if necessary)
 */
static strmap_t *get_info_table(smt2_globals_t *g) {
  strmap_t *hmap;

  hmap = g->info;
  if (hmap == NULL) {
    hmap = (strmap_t *) safe_malloc(sizeof(strmap_t));
    init_strmap(hmap, 0); // default size
    g->info = hmap;
  }

  return hmap;
}


/*
 * For deletion: decrement the reference counter of
 * all avals in the table.
 */
static void info_finalizer(void *aux, strmap_rec_t *r) {
  if (r->val >= 0) {
    aval_decref(aux, r->val);
  }
}

/*
 * Delete the table
 */
static void delete_info_table(smt2_globals_t *g) {
  strmap_t *hmap;

  hmap = g->info;
  if (hmap != NULL) {
    strmap_iterate(hmap, g->avtbl, info_finalizer);
    delete_strmap(hmap);
    safe_free(hmap);
    g->info = NULL;
  }
}


/*
 * Add info:
 * - name = keyword
 * - val = attribute value (in g->avtbl)
 * - if there's info for name already, we overwrite it
 * - val may be -1 (AVAL_NULL)
 */
static void add_info(smt2_globals_t *g, const char *name, aval_t val) {
  strmap_t *info;
  strmap_rec_t *r;
  bool new;

  info = get_info_table(g);
  r = strmap_get(info, name, &new);
  if (!new && r->val >= 0) {
    aval_decref(g->avtbl, r->val);
  }
  r->val = val;
  if (val >= 0) {
    aval_incref(g->avtbl, val);
  }
}


/*
 * Check whether there's an info record for name
 * - if so return its value in *val and return true
 */
static bool has_info(smt2_globals_t *g, const char *name, aval_t *val) {
  strmap_t *info;
  strmap_rec_t *r;

  info = g->info;
  if (info != NULL) {
    r = strmap_find(info, name);
    if (r != NULL) {
      *val = r->val;
      return true;
    }
  }

  return false;
}



/*
 * SET-OPTION SUPPORT
 */

/*
 * Check whether v is a boolean.
 * If so copy its value in *result, otherwise leave result unchanged
 */
static bool aval_is_boolean(attr_vtbl_t *avtbl, aval_t v, bool *result) {
  char *s;

  if (v >= 0 && aval_tag(avtbl, v) == ATTR_SYMBOL) {
    s = aval_symbol(avtbl, v);
    if (strcmp(s, "true") == 0) {
      *result = true;
      return true;
    }
    if (strcmp(s, "false") == 0) {
      *result = false;
      return true;
    }
  }

  return false;
}

/*
 * Check whether v is a rational
 * If so copy its value in *result
 */
static bool aval_is_rational(attr_vtbl_t *avtbl, aval_t v, rational_t *result) {
  if (v >= 0 && aval_tag(avtbl, v) == ATTR_RATIONAL) {
    q_set(result, aval_rational(avtbl, v));
    return true;
  }

  return false;
}



/*
 * Boolean option
 * - name = option name (keyword)
 * - value = value given (in g->avtbl)
 * - *flag = where to set the option
 */
static void set_boolean_option(smt2_globals_t *g, const char *name, aval_t value, bool *flag) {
  if (aval_is_boolean(g->avtbl, value, flag)) {
    report_success();
  } else {
    print_error("option %s requires a Boolean value", name);
  }
}


/*
 * Integer option
 * - name = option name
 * - val = value in (g->avtbl)
 * - *result = where to copy the value
 */
static void set_uint32_option(smt2_globals_t *g, const char *name, aval_t value, uint32_t *result) {
  rational_t aux;
  int64_t x;

  q_init(&aux);
  if (aval_is_rational(g->avtbl, value, &aux) && q_is_integer(&aux)) {
    if (q_is_neg(&aux)) {
      print_error("option %s must be non-negative", name);
    } else if (q_get64(&aux, &x) && x <= (int64_t) UINT32_MAX){
      assert(x >= 0);
      *result = (uint32_t) x;
      report_success();
    } else {
      print_error("integer overflow: value must be at most %"PRIu32, UINT32_MAX);
    }
  } else {
    print_error("option %s requires an integer value", name);
  }
  q_clear(&aux);
}


/*
 * Set/change the output channel:
 * - name = keyword (should be :regular-output-channel
 * - val = value (should be a string)
 */
static void set_output_file(smt2_globals_t *g, const char *name, aval_t value) {
  FILE *f;
  char *file_name;

  if (value >= 0 && aval_tag(g->avtbl, value) == ATTR_STRING) {
    file_name = aval_string(g->avtbl, value);
    f = stdout;
    if (strcmp(file_name, "stdout") != 0) {
      f = fopen(file_name, "a"); // append
      if (f == NULL) {
	print_error("can't open file %s", file_name);
	return;
      }
    }
    close_output_file(g);
    // change out_name
    if (f != stdout) {
      g->out_name = clone_string(file_name);
      string_incref(g->out_name);
    }
    g->out = f;
    report_success();
  } else {
    print_error("option %s requires a string value", name);
  }
}


/*
 * Set/change the diagnostic channel
 * - name = keyword (should be :regular-output-channel
 * - val = value (should be a string)
 */
static void set_error_file(smt2_globals_t *g, const char *name, aval_t value) {
  FILE *f;
  char *file_name;

  if (value >= 0 && aval_tag(g->avtbl, value) == ATTR_STRING) {
    file_name = aval_string(g->avtbl, value);
    f = stderr;
    if (strcmp(file_name, "stderr") != 0) {
      f = fopen(file_name, "a"); // append
      if (f == NULL) {
	print_error("can't open file %s", file_name);
	return;
      }
    }
    close_error_file(g);
    // change name
    if (f != stderr) {
      g->err_name = clone_string(file_name);
      string_incref(g->err_name);
    }
    g->err = f;
    update_trace_file(g);
    report_success();
  } else {
    print_error("option %s requires a string value", name);
  }
}



/*
 * Set the verbosity level
 * - name = keyword (should be :verbosity)
 * - val = value (in g->avtbl)
 */
static void set_verbosity(smt2_globals_t *g, const char *name, aval_t value) {
  rational_t aux;
  int64_t x;

  q_init(&aux);
  if (aval_is_rational(g->avtbl, value, &aux) && q_is_integer(&aux)) {
    if (q_is_neg(&aux)) {
      print_error("option %s must be non-negative", name);
    } else if (q_get64(&aux, &x) && x <= (int64_t) UINT32_MAX) {
      /*
       * x = verbosity level
       */
      g->verbosity = (uint32_t) x;
      update_trace_verbosity(g);
      report_success();
    } else {
      print_error("integer overflow: %s must be at most %"PRIu32, UINT32_MAX);
    }
  } else {
    print_error("option %s requires an integer value", name);
  }
  q_clear(&aux);
}



/*
 * OUTPUT OF INFO AND OPTIONS
 */

/*
 * Print pair (keyword, value)
 */
static void print_kw_string_pair(const char *keyword, const char *value) {
  print_out("(%s \"%s\")\n", keyword, value);
}

static void print_kw_symbol_pair(const char *keyword, const char *value) {
  print_out("(%s %s)\n", keyword, value);
}

static const char * const string_bool[2] = { "false", "true" };

static void print_kw_boolean_pair(const char *keyword, bool value) {
  print_kw_symbol_pair(keyword, string_bool[value]);
}

static void print_kw_uint32_pair(const char *keyword, uint32_t value) {
  print_out("(%s %"PRIu32")\n", keyword, value);
}


/*
 * Print attribute values
 */
static void print_aval(smt2_globals_t *g, aval_t val);

static void print_aval_list(smt2_globals_t *g, attr_list_t *d) {
  uint32_t i, n;

  n = d->nelems;
  assert(n > 0);
  print_out("(");
  print_aval(g, d->data[0]);
  for (i=1; i<n; i++) {
    print_out(" ");
    print_aval(g, d->data[i]);
  }
  print_out(")");
}

/*
 * We can't use bvconst_print here because it uses prefix 0b
 */
static void print_aval_bv(smt2_globals_t *q, bvconst_attr_t *bv) {
  uint32_t n;

  n = bv->nbits;
  assert(n > 0);
  print_out("#b");
  do {
    n --;
    print_out("%u", (unsigned) bvconst_tst_bit(bv->data, n));
  } while (n > 0);
}

static void print_aval_rational(smt2_globals_t *g, rational_t *q) {
  q_print(g->out, q);
  if (ferror(g->out)) {
    failed_output();
  }
}

static void print_aval(smt2_globals_t *g, aval_t val) {
  assert(good_aval(g->avtbl, val));
  switch (aval_tag(g->avtbl, val)) {
  case ATTR_RATIONAL:
    print_aval_rational(g, aval_rational(g->avtbl, val));
    break;

  case ATTR_BV:
    print_aval_bv(g, aval_bvconst(g->avtbl, val));
    break;

  case ATTR_STRING:
    print_out("\"%s\"", aval_string(g->avtbl, val));
    break;

  case ATTR_SYMBOL:
    print_out("%s", aval_symbol(g->avtbl, val));
    break;

  case ATTR_LIST:
    print_aval_list(g, aval_list(g->avtbl, val));
    break;

  case ATTR_DELETED:
    report_bug(g->err);
    break;
  }
}

/*
 * Print pair keyword/val
 */
static void print_kw_value_pair(smt2_globals_t *g, const char *name, aval_t val) {
  if (val < 0) {
    print_out("(%s)\n", name);
  } else {
    print_out("(%s ", name);
    print_aval(g, val);
    print_out(")\n");
  }
}



/*
 * Check whether the logic is set
 * - if not print an error
 */
static bool check_logic(void) {
  if (__smt2_globals.logic_code == SMT_UNKNOWN) {
    print_error("no logic set");
    return false;
  }
  return true;
}


/*
 * Converse: make sure that no logic is set
 * - if it is, print (error "...") and return false
 */
static bool option_can_be_set(const char *option_name) {
  if (__smt2_globals.logic_code != SMT_UNKNOWN) {
    print_error("option %s can't be set now. It must be set before (set-logic ...)", option_name);
    return false;
  }
  return true;
}


/*
 * Output for options we don't support
 */
static void unsupported_option(void) {
  print_out("unsupported\n");
}


/*
 * CONTEXT INITIALIZATION
 */


/*
 * Allocate and initialize the context based on g->logic
 * - make sure the logic is supported before calling this
 */
static void init_smt2_context(smt2_globals_t *g) {
  smt_logic_t logic;
  context_arch_t arch;
  context_mode_t mode;
  bool iflag;
  bool qflag;

  assert(logic_is_supported(g->logic_code));

  // default: assume g->benchmark_mode is false
  logic = g->logic_code;
  mode = CTX_MODE_PUSHPOP;
  arch = arch_for_logic(logic);
  iflag = iflag_for_logic(logic);
  qflag = qflag_for_logic(logic);

  if (g->benchmark_mode) {
    // change mode and arch for QF_IDL/QF_RDL
    mode = CTX_MODE_ONECHECK;
    switch (logic) {
    case QF_IDL:
      arch = CTX_ARCH_AUTO_IDL;
      break;

    case QF_RDL:
      arch = CTX_ARCH_AUTO_RDL;
      break;

    default:
      break;
    }
  }

  g->ctx = yices_create_context(logic, arch, mode, iflag, qflag);
  assert(g->ctx != NULL);
  if (g->verbosity > 0) {
    context_set_trace(g->ctx, get_tracer(g));
  }
}


/*
 * Initialize the search parameters
 * - this must be done after the context is created
 * - if the architecture is AUTO_RDL or AUTO_IDL,
 *   this must be called after the assertions
 */
static void init_search_parameters(smt2_globals_t *g) {
  assert(g->ctx != NULL);
  yices_default_params_for_context(g->ctx, &parameters);
}



/*
 * DELAYED ASSERTION/CHECK_SAT
 */

/*
 * Check whether term t requires the Egraph
 * - seen = hset of all terms seen so far (none of them requires the Egraph)
 */
static bool needs_egraph(int_hset_t *seen, term_t t);

static bool composite_needs_egraph(int_hset_t *seen, composite_term_t *d) {
  uint32_t i, n;

  n = d->arity;
  for (i=0; i<n; i++) {
    if (needs_egraph(seen, d->arg[i])) return true;
  }
  return false;
}

static bool product_needs_egraph(int_hset_t *seen, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    if (needs_egraph(seen, p->prod[i].var)) return true;
  }
  return false;
}

static bool poly_needs_egraph(int_hset_t *seen, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n) {
    if (needs_egraph(seen, p->mono[i].var)) return true;
    i ++;
  }
  return false;
}

static bool bvpoly64_needs_egraph(int_hset_t *seen, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n) {
    if (needs_egraph(seen, p->mono[i].var)) return true;
    i ++;
  }
  return false;
}

static bool bvpoly_needs_egraph(int_hset_t *seen, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n) {
    if (needs_egraph(seen, p->mono[i].var)) return true;
    i ++;
  }
  return false;
}



static bool needs_egraph(int_hset_t *seen, term_t t) {
  term_table_t *terms;
  bool result;

  result = false;
  t = unsigned_term(t); // clear polarity
  if (int_hset_add(seen, t)) {
    // not seen yet
    terms = __yices_globals.terms;
    switch (term_kind(terms, t)) {
    case UNUSED_TERM:
    case RESERVED_TERM:
      assert(false);
      break;

    case CONSTANT_TERM:
    case VARIABLE:
    case UNINTERPRETED_TERM:
      result = is_utype_term(terms, t);
      break;

    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      result = false;
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      result = needs_egraph(seen, arith_atom_arg(terms, t));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case EQ_TERM:
    case DISTINCT_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      result = composite_needs_egraph(seen, composite_term_desc(terms, t));
      break;

    case BIT_TERM:
      result = needs_egraph(seen, bit_term_arg(terms, t));
      break;

    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case FORALL_TERM:
    case LAMBDA_TERM:
    case SELECT_TERM:
      result = true;
      break;

    case POWER_PRODUCT:
      result = product_needs_egraph(seen, pprod_term_desc(terms, t));
      break;

    case ARITH_POLY:
      result = poly_needs_egraph(seen, poly_term_desc(terms, t));
      break;

    case BV64_POLY:
      result = bvpoly64_needs_egraph(seen, bvpoly64_term_desc(terms, t));
      break;

    case BV_POLY:
      result = bvpoly_needs_egraph(seen, bvpoly_term_desc(terms, t));
      break;
    }
  }

  return result;
}

/*
 * Check whether any formula is a[0...n-1] contains an uninterpreted function
 */
static bool has_uf(term_t *a, uint32_t n) {
  int_hset_t seen; // set of visited terms
  bool result;
  uint32_t i;

  result = false;
  init_int_hset(&seen, 32);
  for (i=0; i<n; i++) {
    result = needs_egraph(&seen, a[i]);
    if (result) break;
  }
  delete_int_hset(&seen);

  return result;
}

/*
 * Add a assertion t to g->assertions
 * - do nothing if t is true
 * - if t is false, set g->trivially_unsat to true
 */
static void add_delayed_assertion(smt2_globals_t *g, term_t t) {
  if (t != true_term) {
    ivector_push(&g->assertions, t);
    if (t == false_term) {
      g->trivially_unsat = true;
    }
  }
}


/*
 * Check satisfiability of all assertions
 */
static void check_delayed_assertions(smt2_globals_t *g) {
  int32_t code;
  smt_status_t status;

  // set frozen to true to disable more assertions
  g->frozen = true;

  if (g->trivially_unsat) {
    print_out("unsat\n");
  } else if (g->assertions.size == 0) {
    print_out("sat\n");
  } else {
    /*
     * check for mislabeled benchmarks: some benchmarks
     * marked as QF_UFIDL do not require the Egraph (should be QF_IDL)
     */
    if (g->benchmark_mode && g->logic_code == QF_UFIDL &&
	!has_uf(g->assertions.data, g->assertions.size)) {
      tprintf(g->tracer, 2, "(Warning: switching logic to QF_IDL)\n");
      g->logic_code = QF_IDL;
    }
    init_smt2_context(g);
#if 1
    code = yices_assert_formulas(g->ctx, g->assertions.size, g->assertions.data);
    if (code < 0) {
      // error during assertion processing
      print_yices_error(true);
      return;
    }
    //    yices_print_presearch_stats(stderr, g->ctx);
    //    dump("yices2intern.dmp", g->ctx);

    init_search_parameters(g);
    if (g->random_seed != 0) {
      parameters.random_seed = g->random_seed;
    }

    status = check_context(g->ctx, &parameters);
    switch (status) {
    case STATUS_UNKNOWN:
    case STATUS_UNSAT:
    case STATUS_SAT:
    case STATUS_INTERRUPTED:
      show_status(status);
      break;

    case STATUS_ERROR:
      print_yices_error(true);
      break;

    case STATUS_IDLE:
    case STATUS_SEARCHING:
    default:
      bad_status_bug(g->err);
      break;
    }
#else
    /*
     * FOR TESTING: DISPLAY THE ASSERTIONS
     * (Preprocess then print)
     */
    code = context_process_formulas(g->ctx, g->assertions.size, g->assertions.data);
    if (code < 0) {
      print_yices_error(true);
      return;
    }
    pp_context(g->out, g->ctx);
#endif
  }

  flush_out();
}


#if 0
/*
 * FOR TESTING/DEBUGGING: PRINT ALL DELAYED ASSERTIONS
 */
#include "io/term_printer.h"

static void show_delayed_assertions(smt2_globals_t *g) {
  yices_pp_t printer;
  term_t *v;
  uint32_t i, n;

  if (g->benchmark_mode) {
    v = g->assertions.data;
    n = g->assertions.size;

    init_pretty_printer(&printer, g);
    for (i=0; i<n; i++) {
      pp_term_full(&printer, __yices_globals.terms, v[i]);
      flush_yices_pp(&printer);
    }
    delete_yices_pp(&printer, true);
  }
}

#endif

/*
 * CONTEXT OPERATIONS: INCREMENTAL MODE
 */

/*
 * Assert t in g->ctx
 * - t is known to be a Boolean term here
 */
static void add_assertion(smt2_globals_t *g, term_t t) {
  int32_t code;

  assert(g->ctx != NULL && context_supports_pushpop(g->ctx));

  switch (context_status(g->ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    // cleanup model and return to IDLE
    if (g->model != NULL) {
      yices_free_model(g->model);
      g->model = NULL;
    }
    context_clear(g->ctx);
    assert(context_status(g->ctx) == STATUS_IDLE);
    // fall through intended

  case STATUS_IDLE:
    code = assert_formula(g->ctx, t);
    if (code < 0) {
      print_yices_error(true);
    } else {
      report_success();
    }
    break;

  case STATUS_UNSAT:
    /*
     * Ignore the assertion. We don't try to check whether
     * t is a correct assertion (e.g., no free variables in f).
     */
    report_success();
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  default:
    bad_status_bug(g->err);
    break;
  }

}


/*
 * Check satisfiability
 */
static void ctx_check_sat(smt2_globals_t *g) {
  smt_status_t stat;

  assert(g->ctx != NULL && context_supports_pushpop(g->ctx));

  stat = context_status(g->ctx);
  switch (stat) {
  case STATUS_UNKNOWN:
  case STATUS_UNSAT:
  case STATUS_SAT:
    // already solved: print the status
    show_status(stat);
    break;

  case STATUS_IDLE:
    // change the seed if needed
    if (g->random_seed != 0) {
      parameters.random_seed = g->random_seed;
    }
    stat = check_context(g->ctx, &parameters);
    show_status(stat);
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  default:
    bad_status_bug(g->err);
    break;
  }
  flush_out();
}


/*
 * New assertion scope
 */
static void ctx_push(smt2_globals_t *g) {
  assert(g->ctx != NULL && context_supports_pushpop(g->ctx));

  switch (context_status(g->ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    // cleanup model and return to IDLE
    if (g->model != NULL) {
      yices_free_model(g->model);
      g->model = NULL;
    }
    context_clear(g->ctx);
    assert(context_status(g->ctx) == STATUS_IDLE);
    // fall through intended

  case STATUS_IDLE:
    context_push(g->ctx);
    break;

  case STATUS_UNSAT:
    g->pushes_after_unsat ++;
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  default:
    bad_status_bug(g->err);
    break;
  }
}


/*
 * Backtrack to the previous scope
 */
static void ctx_pop(smt2_globals_t *g) {
  assert(g->ctx != NULL && context_supports_pushpop(g->ctx));

  switch (context_status(g->ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    // delete the model if any
    if (g->model != NULL) {
      yices_free_model(g->model);
      g->model = NULL;
    }
    context_clear(g->ctx);
    assert(context_status(g->ctx) == STATUS_IDLE);
    // fall-through intended

  case STATUS_IDLE:
    context_pop(g->ctx);
    break;

  case STATUS_UNSAT:
    assert(g->model == NULL);
    if (g->pushes_after_unsat > 0) {
      g->pushes_after_unsat --;
    } else {
      context_clear_unsat(g->ctx);
      context_pop(g->ctx);
    }
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  default:
    bad_status_bug(g->err);
    break;
  }
}


/*
 * MODELS AND PRINT VALUES
 */

/*
 * Try to construct the model of the current set of assertions
 * - return NULL and print an error if the context status is neither
 *   SAT nor UNKNOWN
 *
 * In non-interactive mode: there may not be a context at this point.
 */
static model_t *get_model(smt2_globals_t *g) {
  model_t *mdl;

  mdl = g->model;
  if (mdl == NULL) {
    if (g->ctx == NULL)  {
      // benchmark mode: no context
      assert(g->benchmark_mode);

      if (!g->frozen) {
	print_error("can't build a model. Call (check-sat) first");
      } else if (g->trivially_unsat) {
	print_error("the context is unsatisfiable");
      } else {
	assert(g->assertions.size == 0);
	// no assertions: build a trivial model
	// we set keep_subst to true to be consistent
	mdl = yices_new_model(true);
      }

    } else {
      // context exists
      switch (context_status(g->ctx)) {
      case STATUS_UNKNOWN:
      case STATUS_SAT:
	mdl = yices_get_model(g->ctx, true);
	break;

      case STATUS_UNSAT:
	print_error("the context is unsatisfiable");
	break;

      case STATUS_IDLE:
	print_error("can't build a model. Call (check-sat) first");
	break;

      case STATUS_SEARCHING:
      case STATUS_INTERRUPTED:
      default:
	print_out("BUG: unexpected context status");
	report_bug(__smt2_globals.err);
	break;
      }
    }
    g->model = mdl;
  }

  return mdl;
}


/*
 * Print value (<SMT2-expression> <value>)
 * - printer = pretty printer object
 * - vtbl = value table where v is stored
 * - token_queue = whatever was parsed
 * - i = index of the SMT2 expression for t in token_queue
 */
static void print_term_value(yices_pp_t *printer, value_table_t *vtbl, etk_queue_t *token_queue, value_t v, int32_t i) {
  pp_open_block(printer, PP_OPEN_PAR);
  pp_smt2_expr(printer, token_queue, i);
  smt2_pp_object(printer, vtbl, v);
  pp_close_block(printer, true);
}


/*
 * Print a list of pairs terms/values
 * - the list of terms an array of n expression indices expr[0..n-1]
 *   where expr[i] is an valid start index in token_queue
 * - the corresponding values as in v[0 ... n-1]
 */
static void print_term_value_list(yices_pp_t *printer, value_table_t *vtbl, etk_queue_t *token_queue,
				  int32_t *expr, value_t *v, uint32_t n) {
  uint32_t i;
  value_t x, u;

  u = vtbl_mk_unknown(vtbl);

  pp_open_block(printer, PP_OPEN_VPAR); // open '('
  for (i=0; i<n; i++) {
    x = v[i];
    if (x < 0) x = u;
    print_term_value(printer, vtbl, token_queue, x, expr[i]);
  }
  pp_close_block(printer, true); // close ')'
}


/*
 * Evaluate the value of an array of terms in mdl
 * - n = size of array t
 * - the values are added to vector v
 * - so the value for term t[i] is stored in v->data[i]
 * - v->data[i] may be a negative error code if the value can't be
 *   computed
 */
static void evaluate_term_values(model_t *mdl, term_t *t, uint32_t n, ivector_t *v) {
  evaluator_t evaluator;
  uint32_t i;
  value_t x;

  /*
   * We store all values (even the error codes)
   * We could stop on the first error?
   */
  ivector_reset(v);
  resize_ivector(v, n);
  init_evaluator(&evaluator, mdl);
  for (i=0; i<n; i++) {
    x = eval_in_model(&evaluator, t[i]);
    ivector_push(v, x);
  }
  delete_evaluator(&evaluator);
}


/*
 * GET ASSIGNMENT
 */

/*
 * Print pair (name val) where val is a Boolean value
 */
static void print_bool_assignment(yices_pp_t *printer, const char *name, bval_t val) {
  pp_open_block(printer, PP_OPEN_PAR); // '('
  pp_string(printer, name);
  if (bval_is_undef(val)) {
    pp_string(printer, "???");
  } else {
    pp_bool(printer, bval2bool(val));
  }
  pp_close_block(printer, true); // close ')'
}


/*
 * Trivial assignment: this is called when Yices is used in benchmark
 * mode, and all assertions simplify to true. In this case, the
 * assertions are trivially satisfiable but no context is
 * constructed. We just go through the list of all named Booleans and
 * give them the same value (UNDEF), except if any of them is equal to
 * true or false.
 */
static bval_t trivial_bool_value(term_t t) {
  bval_t v;

  v = VAL_UNDEF_FALSE;
  if (t == true_term) {
    v = VAL_TRUE;
  } else if (t == false_term) {
    v = VAL_FALSE;
  }

  return v;
}

static void print_trivial_assignment(yices_pp_t *printer, named_term_stack_t *s) {
  uint32_t i, n;
  bval_t v;

  pp_open_block(printer, PP_OPEN_VPAR);  // open '('
  n = s->top;
  for (i=0; i<n; i++) {
    v = trivial_bool_value(s->data[i].term);
    print_bool_assignment(printer, s->data[i].name, v);
  }
  pp_close_block(printer, true);  // close ')'
}


/*
 * Non-trivial assignment: go through the list of all named Booleans
 * - query the context to get each term value
 * - if a value is unknown, print the default 'true'
 */
static void print_assignment(yices_pp_t *printer, context_t *ctx, named_term_stack_t *s) {
  uint32_t i, n;
  bval_t v;

  pp_open_block(printer, PP_OPEN_VPAR);
  n = s->top;
  for (i=0; i<n; i++) {
    v = context_bool_term_value(ctx, s->data[i].term);
    print_bool_assignment(printer, s->data[i].name, v);
  }
  pp_close_block(printer, true);
}



/*
 * Show assignment of all named booleans
 * - check whether we have a context first
 */
static void show_assignment(smt2_globals_t *g) {
  yices_pp_t printer;

  if (g->ctx == NULL) {
    assert(g->benchmark_mode);

    if (!g->frozen) {
      print_error("can't build the assignment. Call (check-sat) first");
    } else if (g->trivially_unsat) {
      print_error("the context is unsatisfiable");
    } else {
      assert(g->assertions.size == 0);
      // trivially sat
      init_pretty_printer(&printer, g);
      print_trivial_assignment(&printer, &g->named_bools);
      delete_yices_pp(&printer, true);
    }

  } else {
    switch (context_status(g->ctx)) {
    case STATUS_UNKNOWN:
    case STATUS_SAT:
      init_pretty_printer(&printer, g);
      print_assignment(&printer, g->ctx, &g->named_bools);
      delete_yices_pp(&printer, true);
      break;

    case STATUS_UNSAT:
      print_error("the context is unsatisfiable");
      break;

    case STATUS_IDLE:
      print_error("can't build the assignment. Call (check-sat) first");
      break;

    case STATUS_SEARCHING:
    case STATUS_INTERRUPTED:
    default:
      print_out("BUG: unexpected context status");
      report_bug(__smt2_globals.err);
      break;
    }
  }
}



/*
 * DECLARATIONS AND PUSH/POP
 */

/*
 * If global_decls is false and the push/pop stack is not empty, push a
 * name onto a name stack so that we can remove the declaration on pop.
 *
 * NOTE: s is cloned twice: once to be stored in the term/type/macro
 * symbol tables and once more here. Maybe we could optimize this.
 */
static void save_name(smt2_globals_t *g, smt2_name_stack_t *name_stack, const char *s) {
  char *clone;

  if (!g->global_decls && smt2_stack_is_nonempty(&g->stack)) {
    clone = clone_string(s);
    smt2_push_name(name_stack, clone);
  }
}

static inline void save_term_name(smt2_globals_t *g, const char *s) {
  save_name(g, &g->term_names, s);
}

static inline void save_type_name(smt2_globals_t *g, const char *s) {
  save_name(g, &g->type_names, s);
}

static inline void save_macro_name(smt2_globals_t *g, const char *s) {
  save_name(g, &g->macro_names, s);
}



/*
 * For debugging: check that the stack look reasonable
 */
#ifndef NDEBUG

static void check_stack(smt2_globals_t *g) {
  smt2_stack_t *stack;
  uint64_t sum;
  uint32_t i;

  if (g->ctx != NULL) {
    stack = &g->stack;
    // check that stack->levels is correct
    sum = 0;
    for (i=0; i<stack->top; i++) {
      sum += stack->data[i].multiplicity;
    }
    if (sum != stack->levels) {
      print_error("Invalid stack: levels don't match");
      report_bug(g->err);
    }

    if (context_base_level(g->ctx) + g->pushes_after_unsat != stack->top) {
      print_error("Invalid stack: push counters don't match");
      report_bug(g->err);
    }

    if (g->pushes_after_unsat > 0 && context_status(g->ctx) != STATUS_UNSAT) {
      print_error("Invalid stack: push_after_unsat is positive but context is not unsat");
      report_bug(g->err);
    }
  }
}

#else

// Do nothing
static inline void check_stack(smt2_globals_t *g) {
}

#endif


/*
 * EXPLANATION FOR UNKNOWN STATUS
 */

/*
 * We check whether the context status is STAT_UNKNOWN
 * if so we print (:reason-unknown incomplete).
 *
 * Otherwise print an error
 */
static void explain_unknown_status(smt2_globals_t *g) {
  if (check_logic()) {
    if (g->ctx == NULL) {
      // benchmark mode: no context
      assert(g->benchmark_mode);

      if (!g->frozen) {
	print_error("can't tell until you call (check-sat)");
      } else if (g->trivially_unsat) {
	print_error("the context is unsatisfiable");
      } else {
	assert(g->assertions.size == 0);
	print_error("the context is satisfiable");
      }
    } else {
      switch (context_status(g->ctx)) {
      case STATUS_UNKNOWN:
	print_kw_symbol_pair(":reason-unknown", "incomplete");
	flush_out();
	break;

      case STATUS_SAT:
	print_error("the context is satisfiable");
	break;

      case STATUS_UNSAT:
	print_error("the context is unsatisfiable");
	break;

      case STATUS_IDLE:
	print_error("can't tell until you call (check-sat)");
	break;

      case STATUS_SEARCHING:
      case STATUS_INTERRUPTED:
      default:
	print_out("BUG: unexpected context status");
	report_bug(__smt2_globals.err);
	break;
      }
    }
  }
}



/*
 * MAIN CONTROL FUNCTIONS
 */

/*
 * Initialize g to defaults
 */
static void init_smt2_globals(smt2_globals_t *g) {
  g->logic_code = SMT_UNKNOWN;
  g->benchmark_mode = false;
  g->global_decls = false;
  g->pushes_after_unsat = 0;
  g->logic_name = NULL;
  g->out = stdout;
  g->err = stderr;
  g->out_name = NULL;
  g->err_name = NULL;
  g->tracer = NULL;
  g->print_success = false;  // the standard says that this should be true??
  g->expand_definitions = false;
  g->interactive_mode = false;
  g->produce_proofs = false;
  g->produce_unsat_cores = false;
  g->produce_models = false;
  g->produce_assignments = false;
  g->random_seed = 0;  // 0 means any seed is good
  g->verbosity = 0;
  g->avtbl = NULL;
  g->info = NULL;
  g->ctx = NULL;
  g->model = NULL;

  init_smt2_stack(&g->stack);
  init_smt2_name_stack(&g->term_names);
  init_smt2_name_stack(&g->type_names);
  init_smt2_name_stack(&g->macro_names);

  init_named_term_stack(&g->named_bools);
  init_named_term_stack(&g->named_asserts);

  init_etk_queue(&g->token_queue);
  init_ivector(&g->token_slices, 0);
  init_ivector(&g->val_vector, 0);

  // print area for get-value
  //  g->pp_area.width = 120;
  g->pp_area.width = 160;
  g->pp_area.height = UINT32_MAX;
  g->pp_area.offset = 0;
  g->pp_area.stretch = false;
  g->pp_area.truncate = false;

  init_cmd_stats(&g->stats);

  init_ivector(&g->assertions, 0);
  g->trivially_unsat = false;
  g->frozen = false;
}


/*
 * Cleanup: close out and err if different from the defaults
 * - delete all internal structures (except avtbl)
 */
static void delete_smt2_globals(smt2_globals_t *g) {
  delete_info_table(g);
  if (g->logic_name != NULL) {
    string_decref(g->logic_name);
    g->logic_name = NULL;
  }
  if (g->ctx != NULL) {
    yices_free_context(g->ctx);
    g->ctx = NULL;
  }
  if (g->model != NULL) {
    yices_free_model(g->model);
    g->model = NULL;
  }
  delete_ivector(&g->assertions);

  delete_smt2_stack(&g->stack);
  delete_smt2_name_stack(&g->term_names);
  delete_smt2_name_stack(&g->type_names);
  delete_smt2_name_stack(&g->macro_names);

  delete_named_term_stack(&g->named_bools);
  delete_named_term_stack(&g->named_asserts);

  delete_etk_queue(&g->token_queue);
  delete_ivector(&g->token_slices);
  delete_ivector(&g->val_vector);

  close_output_file(g);
  close_error_file(g);
  delete_tracer(g);
}


/*
 * Initialize all internal structures
 * - benchmark: if true, the input is assumed to be an SMT-LIB 2.0 benchmark
 *   (i.e., a set of assertions followed by a single call to check-sat)
 *   In this mode,
 *   - destructive simplifications are allowed.
 *   - push/pop are not supported
 *   - assert can't be used after (check-sat)
 *
 * - print_success = initial setting of the :print-success option.
 *
 * This function is called after yices_init so all Yices internals are ready
 */
void init_smt2(bool benchmark, bool print_success) {
  done = false;
  init_smt2_globals(&__smt2_globals);
  init_attr_vtbl(&avtbl);
  __smt2_globals.avtbl = &avtbl;
  if (benchmark) {
    __smt2_globals.benchmark_mode = true;
    __smt2_globals.global_decls = true;
  }
  __smt2_globals.print_success = print_success;
  check_stack(&__smt2_globals);
}


/*
 * Force verbosity level to k
 */
void smt2_set_verbosity(uint32_t k) {
  __smt2_globals.verbosity = k;
  update_trace_verbosity(&__smt2_globals);
}

/*
 * Display all statistics
 */
void smt2_show_stats(void) {
  show_statistics(&__smt2_globals);
}


/*
 * Delete all structures and close output/trace files
 */
void delete_smt2(void) {
  delete_smt2_globals(&__smt2_globals);
  delete_attr_vtbl(&avtbl); // must be done last
}


/*
 * Check whether the smt2 solver is ready
 * - this must be true after init_smt2()
 * - this must return false if smt2_exit has been called or after
 *   an unrecoverable error
 */
bool smt2_active(void) {
  return !done;
}


/*
 * TOP-LEVEL SMT2 COMMANDS
 */

/*
 * Print number of calls to a command
 * - cmd = name of this command
 * - calls = number of calls
 */
static void tprint_calls(const char *cmd, uint32_t calls) {
  if (calls == 1) {
    tprintf(__smt2_globals.tracer, 12, "\n(%s: 1 call)\n", cmd);
  } else {
    tprintf(__smt2_globals.tracer, 12, "\n(%s: %"PRIu32" calls)\n", cmd, calls);
  }
}

/*
 * Exit function
 */
void smt2_exit(void) {
  done = true;
  report_success();
}


/*
 * Variant: for end-of-file
 */
void smt2_silent_exit(void) {
  done = true;
}


/*
 * Show all formulas asserted so far
 */
void smt2_get_assertions(void) {
  if (check_logic()) {
    print_error("get-assertions is not supported");
  }
}


/*
 * Show the truth value of named Boolean terms
 * (i.e., those that have a :named attribute)
 *
 * Note: the standard says that we should report an error if
 * :produce-assignments is false. We ignore this requirement.
 */
void smt2_get_assignment(void) {
  __smt2_globals.stats.num_get_assignment ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("get-assignment", __smt2_globals.stats.num_get_assignment);

  if (check_logic()) {
    show_assignment(&__smt2_globals);
  }
}


/*
 * Show a proof when context is unsat
 */
void smt2_get_proof(void) {
  if (check_logic()) {
    print_error("get-proof is not supported");
  }
}


/*
 * Get the unsat core: subset of :named assertions that form an unsat core
 */
void smt2_get_unsat_core(void) {
  if (check_logic()) {
    print_error("get-unsat-core is not supported");
  }
}


/*
 * Get the values of terms in the model
 * - the terms are listed in array a
 * - n = number of elements in the array
 *
 * The standard says that we should print an error
 * if :produce-models is false. We don't care about this.
 */
void smt2_get_value(term_t *a, uint32_t n) {
  yices_pp_t printer;
  etk_queue_t *queue;
  ivector_t *slices;
  ivector_t *values;
  model_t *mdl;

  __smt2_globals.stats.num_get_value ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("get-value", __smt2_globals.stats.num_get_value);

  if (check_logic()) {
    // make sure we have a model
    mdl = get_model(&__smt2_globals);
    if (mdl == NULL) return;

    // evaluate all terms: store the values in values->data[0 ... n-1]
    values = &__smt2_globals.val_vector;
    evaluate_term_values(mdl, a, n, values);

    queue = &__smt2_globals.token_queue;
    slices = &__smt2_globals.token_slices;
    assert(slices->size == 0);
    assert(good_token(queue, 2) && start_token(queue, 2));
    collect_subexpr(queue, 2, slices);
    assert(slices->size == n);

    init_pretty_printer(&printer, &__smt2_globals);
    print_term_value_list(&printer, &mdl->vtbl, queue, slices->data, values->data, n);
    delete_yices_pp(&printer, true);
    vtbl_empty_queue(&mdl->vtbl); // cleanup the internal queue
    ivector_reset(slices);
    ivector_reset(values);
  }
}


/*
 * Wrapper around strlen:
 * - strlen(s) has type size_t, which may be larger than 32bits
 * - just in case somebody provides a giant string, we use
 *   this wrapper to truncate the length to a 32bit number if it's really big
 * - big means more than MAX_KW_LEN, which can be any constant larger
 *   than the largest keyword defined in smt2_keywords.txt
 */
#define MAX_KW_LEN ((size_t) 1000000)

static uint32_t kwlen(const char *s) {
  size_t l;

  l = strlen(s);
  if (l > MAX_KW_LEN) {
    l = MAX_KW_LEN;
  }
  return (uint32_t) l;
}


/*
 * Get the value of an option
 * - name = option name (a keyword)
 */
void smt2_get_option(const char *name) {
  smt2_globals_t *g;
  char *s;
  smt2_keyword_t kw;
  uint32_t n;

  g = &__smt2_globals;
  n = kwlen(name);
  kw = smt2_string_to_keyword(name, n);
  switch (kw) {
  case SMT2_KW_PRINT_SUCCESS:
    print_kw_boolean_pair(name, g->print_success);
    break;

  case SMT2_KW_PRODUCE_MODELS:
    print_kw_boolean_pair(name, g->produce_models);
    break;

  case SMT2_KW_PRODUCE_ASSIGNMENTS:
    print_kw_boolean_pair(name, g->produce_assignments);
    break;

  case SMT2_KW_REGULAR_OUTPUT:
    s = g->out_name;
    if (s == NULL) {
      assert(g->out == stdout);
      s = "stdout";
    }
    print_kw_string_pair(name, s);
    break;

  case SMT2_KW_DIAGNOSTIC_OUTPUT:
    s = g->err_name;
    if (s == NULL) {
      assert(g->err == stderr);
      s = "stderr";
    }
    print_kw_string_pair(name, s);
    break;

  case SMT2_KW_RANDOM_SEED:
    print_kw_uint32_pair(name, g->random_seed);
    break;

  case SMT2_KW_VERBOSITY:
    print_kw_uint32_pair(name, g->verbosity);
    break;

  case SMT2_KW_GLOBAL_DECLS:
    print_kw_boolean_pair(name, g->global_decls);
    break;

  case SMT2_KW_EXPAND_DEFINITIONS:
  case SMT2_KW_INTERACTIVE_MODE:
  case SMT2_KW_PRODUCE_PROOFS:
  case SMT2_KW_PRODUCE_UNSAT_CORES:
  default:
    unsupported_option();
    break;
  }

  flush_out();
}


/*
 * Get some info
 * - name = keyword
 */
void smt2_get_info(const char *name) {
  smt2_globals_t *g;
  smt2_keyword_t kw;
  uint32_t n;
  aval_t value;

  n = kwlen(name);
  kw = smt2_string_to_keyword(name, n);
  switch (kw) {
  case SMT2_KW_ERROR_BEHAVIOR:
    print_kw_symbol_pair(name, error_behavior);
    break;

  case SMT2_KW_NAME:
    print_kw_string_pair(name, yices_name);
    break;

  case SMT2_KW_AUTHORS:
    print_kw_string_pair(name, yices_authors);
    break;

  case SMT2_KW_VERSION:
    print_kw_string_pair(name, yices_version);
    break;

  case SMT2_KW_REASON_UNKNOWN:
    explain_unknown_status(&__smt2_globals);
    break;

  case SMT2_KW_ALL_STATISTICS:
    show_statistics(&__smt2_globals);
    break;

  default:
    g = &__smt2_globals;
    if (has_info(g, name, &value)) {
      print_kw_value_pair(g, name, value);
    } else {
      print_error("no info for %s", name);
    }
    break;
  }

  flush_out();
}


/*
 * Set an option:
 * - name = option name (keyword)
 * - value = value (stored in the attribute_value table)
 *
 * SMT2 allows the syntax (set-option :keyword). In such a case,
 * this function is called with value = NULL_VALUE (i.e., -1).
 */
void smt2_set_option(const char *name, aval_t value) {
  smt2_globals_t *g;
  smt2_keyword_t kw;
  uint32_t n;

  g = &__smt2_globals;
  n = kwlen(name);
  kw = smt2_string_to_keyword(name, n);

  switch (kw) {
  case SMT2_KW_PRINT_SUCCESS:
    // required
    set_boolean_option(g, name, value, &g->print_success);
    break;

  case SMT2_KW_PRODUCE_MODELS:
    // optional: if true, get-value can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_models);
    }
    break;

  case SMT2_KW_PRODUCE_ASSIGNMENTS:
    // optional: if true, get-assignment can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_assignments);
    }
    break;

  case SMT2_KW_REGULAR_OUTPUT:
    // required
    set_output_file(g, name, value);
    break;

  case SMT2_KW_DIAGNOSTIC_OUTPUT:
    // required
    set_error_file(g, name, value);
    break;

  case SMT2_KW_RANDOM_SEED:
    // optional
    set_uint32_option(g, name, value, &g->random_seed);
    break;

  case SMT2_KW_VERBOSITY:
    // optional
    set_verbosity(g, name, value);
    break;

  case SMT2_KW_GLOBAL_DECLS:
    // non-standard option (same as MathSAT)
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->global_decls);
    }
    break;

  case SMT2_KW_EXPAND_DEFINITIONS:
  case SMT2_KW_INTERACTIVE_MODE:
  case SMT2_KW_PRODUCE_PROOFS:
  case SMT2_KW_PRODUCE_UNSAT_CORES:
  default:
    unsupported_option();
    flush_out();
    break;
  }
}


/*
 * Set some info field
 * - same conventions as set_option
 */
void smt2_set_info(const char *name, aval_t value) {
  smt2_keyword_t kw;
  uint32_t n;

  n = kwlen(name);
  kw = smt2_string_to_keyword(name, n);
  switch (kw) {
  case SMT2_KW_ERROR_BEHAVIOR:
  case SMT2_KW_NAME:
  case SMT2_KW_AUTHORS:
  case SMT2_KW_VERSION:
  case SMT2_KW_REASON_UNKNOWN:
  case SMT2_KW_ALL_STATISTICS:
    print_error("can't overwrite %s", name);
    break;

  default:
    add_info(&__smt2_globals, name, value);
    report_success();
    break;
  }
}


/*
 * Set the logic:
 * - name = logic name (using the SMT-LIB conventions)
 */
void smt2_set_logic(const char *name) {
  smt_logic_t code;

  if (__smt2_globals.logic_code != SMT_UNKNOWN) {
    print_error("the logic is already set");
    return;
  }

  code = smt_logic_code(name);
  if (code == SMT_UNKNOWN) {
    print_error("unknown logic: %s", name);
    return;
  }

  if (! logic_is_supported(code)) {
    print_error("logic %s is not supported", name);
    return;
  }

  if (! logic_is_official(code)) {
    tprintf(__smt2_globals.tracer, 2, "(Warning: logic %s is not an official SMT-LIB logic)\n", name);
  }

  smt2_lexer_activate_logic(code);
  __smt2_globals.logic_code = code;
  __smt2_globals.logic_name = clone_string(name);
  string_incref(__smt2_globals.logic_name);

  /*
   * In incremental mode: initialize the context
   */
  if (! __smt2_globals.benchmark_mode) {
    init_smt2_context(&__smt2_globals);
    init_search_parameters(&__smt2_globals);
  }

  report_success();
}




/*
 * Push
 * - n = number of scopes to push
 * - if n = 0, nothing should be done
 */
void smt2_push(uint32_t n) {
  smt2_globals_t *g;

  __smt2_globals.stats.num_push ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("push", __smt2_globals.stats.num_push);

  if (check_logic()) {
    g = &__smt2_globals;
    if (g->benchmark_mode) {
      print_error("push is not allowed in non-incremental mode");
    } else {
      if (n > 0) {
	/*
	 * NOTE: g->stacks.levels is 64 bits and MAX_SMT2_STACK_SIZE
	 * is less than 32bits so smt2_stack_push can't cause a
	 * numerical overflow.
	 */
	 smt2_stack_push(&g->stack, n, g->term_names.top, g->type_names.top, g->macro_names.top,
			 g->named_bools.top, g->named_asserts.top);
	 ctx_push(g);
	 check_stack(g);
      }
      report_success();
    }
  }
}


/*
 * Pop:
 * - n = number of scopes to remove
 * - if n = 0 nothing should be done
 * - if n > total number of scopes then an error should be printed
 *   and nothing done
 */
void smt2_pop(uint32_t n) {
  smt2_globals_t *g;
  smt2_push_rec_t *r;
  uint32_t m;

  __smt2_globals.stats.num_pop ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("pop", __smt2_globals.stats.num_pop);

  if (check_logic()) {
    if (__smt2_globals.benchmark_mode) {
      print_error("pop is not allowed in non-incremental mode");
    } else if (n == 0) {
      // do nothing
      report_success();
    } else {
      g = &__smt2_globals;
      if (n > g->stack.levels) {
	if (g->stack.levels > 1) {
	  print_error("can't pop more than %"PRIu64" levels", g->stack.levels);
	} else if (g->stack.levels > 0) {
	  print_error("can't pop more than one level");
	} else {
	  print_error("pop not allowed at the bottom level");
	}
      } else {
	m = 0; // number of levels removed
	do {
	  r = smt2_stack_top(&g->stack);
	  m += r->multiplicity;

	  // remove declarations: this has no effect if g->global_decls is true
	  smt2_pop_term_names(&g->term_names, r->term_decls);
	  smt2_pop_type_names(&g->type_names, r->type_decls);
	  smt2_pop_macro_names(&g->macro_names, r->macro_decls);

	  // remove the named booleans and named assertions
	  pop_named_terms(&g->named_bools, r->named_bools);
	  pop_named_terms(&g->named_asserts, r->named_asserts);

	  // pop on g->ctx
	  ctx_pop(g);
	  smt2_stack_pop(&g->stack);
	} while (n > m);

	if (n < m) {
	  // push (m - n)
	  smt2_stack_push(&g->stack, m - n, g->term_names.top, g->type_names.top, g->macro_names.top,
			  g->named_bools.top, g->named_asserts.top);
	  ctx_push(g);
	}

	check_stack(g);

	// call the garbage collector
	if (g->term_names.deletions > 1000) {
	  yices_garbage_collect(NULL, 0, NULL, 0, true);
	  g->term_names.deletions = 0;
	}

	report_success();
      }
    }
  }
}


/*
 * Assert one formula t
 * - if t is a :named assertion then it should be recorded for unsat-core
 */
void smt2_assert(term_t t) {
  __smt2_globals.stats.num_assert ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("assert", __smt2_globals.stats.num_assert);

  if (check_logic()) {
    if (yices_term_is_bool(t)) {
      if (__smt2_globals.benchmark_mode) {
	if (__smt2_globals.frozen) {
	  print_error("assertions are not allowed after (check-sat) in non-incremental mode");
	} else {
	  add_delayed_assertion(&__smt2_globals, t);
	  report_success();
	}
      } else {
	add_assertion(&__smt2_globals, t);
      }
    } else {
      // not a Boolean term
      print_error("type error in assert: Boolean term required");
    }
  }
}


/*
 * Check satisfiability of the current set of assertions
 */
void smt2_check_sat(void) {
  __smt2_globals.stats.num_check_sat ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("check-sat", __smt2_globals.stats.num_check_sat);

  if (check_logic()) {
    if (__smt2_globals.benchmark_mode) {
      if (__smt2_globals.frozen) {
	print_error("multiple calls to (check-sat) are not allowed in non-incremental mode");
      } else {
	// PROVISIONAL
	//	show_delayed_assertions(&__smt2_globals);
	check_delayed_assertions(&__smt2_globals);
      }
    } else {
      ctx_check_sat(&__smt2_globals);
    }
  }
}


/*
 * Declare a new sort:
 * - name = sort name
 * - arity = arity
 *
 * If arity is 0, this defines a new uninterpreted type.
 * Otherwise, this defines a new type constructor.
 */
void smt2_declare_sort(const char *name, uint32_t arity) {
  type_t tau;
  int32_t macro;

  __smt2_globals.stats.num_declare_sort ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("declare-sort", __smt2_globals.stats.num_declare_sort);

  if (check_logic()) {
    if (arity == 0) {
      tau = yices_new_uninterpreted_type();
      yices_set_type_name(tau, name);
      save_type_name(&__smt2_globals, name);
      report_success();
    } else {
      macro = yices_type_constructor(name, arity);
      if (macro < 0) {
	print_yices_error(true);
      } else {
	save_macro_name(&__smt2_globals, name);
	report_success();
      }
    }
  }

}


/*
 * Define a new type macro
 * - name = macro name
 * - n = number of variables
 * - var = array of type variables
 * - body = type expressions
 */
void smt2_define_sort(const char *name, uint32_t n, type_t *var, type_t body) {
  int32_t macro;

  __smt2_globals.stats.num_define_sort ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("define-sort", __smt2_globals.stats.num_define_sort);

  if (check_logic()) {
    if (n == 0) {
      yices_set_type_name(body, name);
      save_type_name(&__smt2_globals, name);
      report_success();
    } else {
      macro = yices_type_macro(name, n, var, body);
      if (macro < 0) {
	print_yices_error(true);
      } else {
	save_macro_name(&__smt2_globals, name);
	report_success();
      }
    }
  }
}


/*
 * Declare a new uninterpreted function symbol
 * - name = function name
 * - n = arity + 1
 * - tau = array of n types
 *
 * If n = 1, this creates an uninterpreted constant of type tau[0]
 * Otherwise, this creates an uninterpreted function of type
 * tau[0] x ... x tau[n-1] to tau[n]
 */
void smt2_declare_fun(const char *name, uint32_t n, type_t *tau) {
  term_t t;
  type_t sigma;

  assert(n > 0);

  __smt2_globals.stats.num_declare_fun ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("declare-fun", __smt2_globals.stats.num_declare_fun);

  if (check_logic()) {
    n --;
    sigma = tau[n]; // range
    if (n > 0) {
      sigma = yices_function_type(n, tau, sigma);
    }
    assert(sigma != NULL_TYPE);

    t = yices_new_uninterpreted_term(sigma);
    assert(t != NULL_TERM);
    yices_set_term_name(t, name);
    save_term_name(&__smt2_globals, name);

    report_success();
  }
}


/*
 * Define a function
 * - name = function name
 * - n = arity
 * - var = array of n term variables
 * - body = term
 * - tau = expected type of body
 *
 * If n = 0, this is the same as (define <name> :: <type> <body> )
 * Otherwise, a lambda term is created.
 */
void smt2_define_fun(const char *name, uint32_t n, term_t *var, term_t body, type_t tau) {
  term_t t;

  __smt2_globals.stats.num_define_fun ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("define-fun", __smt2_globals.stats.num_define_fun);

  if (check_logic()) {
    if (! yices_check_term_type(body, tau)) {
      // ? print a better error message?
      print_yices_error(true);
      return;
    }

    /*
     * because of the annoying :named annotation
     * the name could be assigned now (even though
     * it was not when (define name ...)) was processed
     */
    if (yices_get_term_by_name(name) != NULL_TERM) {
      if (symbol_needs_quotes(name)) {
	print_error("Invalid definition: can't (define |%s| ...) and use |%s| in a :named annotation",
		    name, name);
      } else {
	print_error("Invalid definition: can't (define %s ...) and use %s in a :named annotation",
		    name, name);
      }
      return;
    }

    t = body;
    if (n > 0) {
      t = yices_lambda(n, var, t);
      if (t < 0) {
	print_yices_error(true);
	return;
      }
    }
    yices_set_term_name(t, name);
    save_term_name(&__smt2_globals, name);

    report_success();
  }
}


/*
 * EXTENSIONS/NON-STANDARD COMMANDS
 */

/*
 * Show the model if any
 */
void smt2_get_model(void) {
  yices_pp_t printer;
  model_t *mdl;

  if (check_logic()) {
    mdl = get_model(&__smt2_globals);
    if (mdl == NULL) return;

    init_pretty_printer(&printer, &__smt2_globals);
    smt2_pp_full_model(&printer, mdl);
    delete_yices_pp(&printer, true);
  }
}


/*
 * Print s on the output channel
 */
void smt2_echo(const char *s) {
  print_out("%s\n", s);
  flush_out();
}


/*
 * Full reset:
 * - delete all assertions, terms, types, and declarations
 */
void smt2_reset(void) {
  smt2_globals_t *g;

  if (check_logic()) {
    g = &__smt2_globals;
    if (g->benchmark_mode) {
      print_error("reset is not allowed in non-incremental mode");
    } else {
      /*
       * Reset context, model and internal stacks
       * + all auxiliary vectors
       *
       * Keep options + logic_name + output/diagnostic channels
       * + info_table and attribute table.
       */
      g->pushes_after_unsat = 0;

      assert(g->ctx != NULL);
      yices_free_context(g->ctx);
      g->ctx = NULL;

      if (g->model != NULL) {
	yices_free_model(g->model);
	g->model = NULL;
      }

      reset_smt2_stack(&g->stack);
      reset_smt2_name_stack(&g->term_names);
      reset_smt2_name_stack(&g->type_names);
      reset_smt2_name_stack(&g->macro_names);

      reset_named_term_stack(&g->named_bools);
      reset_named_term_stack(&g->named_asserts);

      reset_etk_queue(&g->token_queue);
      ivector_reset(&g->token_slices);
      ivector_reset(&g->val_vector);

      yices_reset_tables();

      // build a fresh empty context
      init_smt2_context(g);

      report_success();
    }
  }
}


/*
 * ATTRIBUTES
 */

/*
 * Add a :named attribute to term t
 * - t is a ground term
 * - name is a free term symbol
 * - op = enclosing operator of (! t :named name ..)
 * - for a named assertion, op is SMT2_ASSERT
 */
void smt2_add_name(int32_t op, term_t t, const char *name) {
  char *clone;

  // add the mapping name --> t
  yices_set_term_name(t, name);
  save_term_name(&__smt2_globals, name);

  // special processing for Boolean terms
  if (yices_term_is_bool(t)) {
    // named booleans (for get-assignment)
    clone = clone_string(name);
    push_named_term(&__smt2_globals.named_bools, t, clone);

    // named assertions (for unsat cores)
    if (op == SMT2_ASSERT && __smt2_globals.produce_unsat_cores) {
      push_named_term(&__smt2_globals.named_asserts, t, clone);
    }
  }
}



/*
 * Add a :pattern attribute to term t
 * - the pattern is an array p of n terms
 * - op = enclosing operator of (! t :pattern ....)
 * - for a quantified term, op is either MK_EXISTS or MK_FORALL
 */
void smt2_add_pattern(int32_t op, term_t t, term_t *p, uint32_t n) {
  // TBD
}
