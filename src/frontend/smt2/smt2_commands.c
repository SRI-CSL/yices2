/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
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

#include "api/context_config.h"
#include "api/smt_logic_codes.h"
#include "api/yices_extensions.h"
#include "api/yices_globals.h"
#include "api/yices_mutex.h"
#include "context/context.h"
#include "frontend/common/bug_report.h"
#include "frontend/common/parameters.h"
#include "frontend/common/tables.h"
#include "frontend/smt2/attribute_values.h"
#include "frontend/smt2/smt2_commands.h"
#include "frontend/smt2/smt2_model_printer.h"
#include "frontend/smt2/smt2_printer.h"
#include "io/term_printer.h"
#include "frontend/smt2/smt2_symbol_printer.h"
#include "mcsat/options.h"
#include "model/model_eval.h"
#include "model/projection.h"
#include "solvers/bv/dimacs_printer.h"
#include "utils/refcount_strings.h"
#include "utils/timeout.h"

#include "yices.h"
#include "yices_exit_codes.h"

// for statistics
#include "io/simple_printf.h"
#include "solvers/bv/bvsolver.h"
#include "solvers/floyd_warshall/idl_floyd_warshall.h"
#include "solvers/floyd_warshall/rdl_floyd_warshall.h"
#include "solvers/funs/fun_solver.h"
#include "solvers/quant/quant_solver.h"
#include "solvers/simplex/simplex.h"
#include "utils/cputime.h"
#include "utils/memsize.h"


//for ian's threading hacks
#include "mt/threads.h"
#include "mt/thread_macros.h"

#include "frontend/smt2/smt2_term_utils.h"

#include "utils/int_hash_map.h"

/*
 * DUMP CONTEXT: FOR TESTING/DEBUGGING
 */
#define DUMP_CTX 0

#if DUMP_CTX

#include "io/term_printer.h"
#include "io/type_printer.h"
#include "solvers/floyd_warshall/idl_fw_printer.h"
#include "solvers/floyd_warshall/rdl_fw_printer.h"
#include "solvers/simplex/simplex_printer.h"
#include "solvers/bv/bvsolver_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/cdcl/gates_printer.h"
#include "context/context_printer.h"


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
    print_gate_table(f, solver->blaster->htbl);
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


/*
 * BITBLAST THEN EXPORT TO DIMACS
 */

/*
 * Export ctx content in DIMACS format
 * - s = file name
 */
static void do_export(context_t *ctx, const char *s) {
  FILE *f;

  f = fopen(s, "w");
  if (f == NULL) {
    perror(s);
    exit(YICES_EXIT_SYSTEM_ERROR);
  } else {
    dimacs_print_bvcontext(f, ctx);
    fclose(f);
  }
}

/*
 * Force bitblasting then export
 * - s = filename
 */
static void bitblast_then_export(context_t *ctx, const char *s) {
  smt_status_t stat;

  stat = precheck_context(ctx);
  switch (stat) {
  case STATUS_UNKNOWN:
    do_export(ctx, s);
    break;

  case STATUS_SAT:
    fprintf(stderr, "Trivially sat: Export to dimacs skipped\n");
    break;
  case STATUS_UNSAT:
    fprintf(stderr, "Trivially unsat: Export to dimacs skipped\n");
    break;

  case YICES_STATUS_INTERRUPTED:
    fprintf(stderr, "Export to dimacs interrupted\n");
    break;

  default:
    fprintf(stderr, "Unexpected context status after pre-check\n");
    break;
  }
}


/*
 * Export the delayed assertions
 * - ctx = context
 * - a = array of n formulas (the assertions)
 * - s = filename
 */
static int32_t export_delayed_assertions(context_t *ctx, uint32_t n, term_t *a, const char *s) {
  int32_t code;

  code = CTX_OPERATION_NOT_SUPPORTED;
  if (ctx->logic == QF_BV && ctx->mode == CTX_MODE_ONECHECK) {
    code = yices_assert_formulas(ctx, n, a);
    if (code == 0) {
      bitblast_then_export(ctx, s);
    }
  }
  return code;
}




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
 * PATTERN MAP
 */

/*
 * Initialize; nothing allocated yet
 */
static void init_smt2_pattern_map(ptr_hmap_t *m) {
  init_ptr_hmap(m, 0);
}

/*
 * Deletion
 */
static void delete_smt2_pattern_map(ptr_hmap_t *m) {
  ptr_hmap_pair_t *p;

  for (p = ptr_hmap_first_record(m);
       p != NULL;
       p = ptr_hmap_next_record(m, p)) {
    ivector_t* list_vector = p->val;
    if (list_vector != NULL) {
      delete_ivector(list_vector);
      safe_free(list_vector);
    }
  }
  delete_ptr_hmap(m);
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
static inline smt2_push_rec_t *smt2_stack_top(const smt2_stack_t *s) {
  assert(s->top > 0);
  return s->data + (s->top - 1);
}


static inline bool smt2_stack_is_nonempty(const smt2_stack_t *s) {
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
 * CHECK AND BUILD A CORE
 */

/*
 * Check sat with model assumptions and build the interpolant
 */
static smt_status_t check_with_model(context_t *ctx, const param_t *params, uint32_t n, const term_t vars[], const term_t values[]) {
  uint32_t i;
  term_t x;
  value_t x_value;
  ivector_t assumptions;
  smt_status_t status;
  model_t mdl;
  evaluator_t mdl_evaluator;

  // Init model and evaluation
  init_model(&mdl, ctx->terms, true);
  init_evaluator(&mdl_evaluator, &mdl);

  // Copy over to model
  init_ivector(&assumptions, n);
  for (i = 0; i < n; ++ i) {
    x = vars[i];
    x_value = eval_in_model(&mdl_evaluator, values[i]);
    model_map_term(&mdl, x, x_value);
    ivector_push(&assumptions, x);
  }

  // Solve
  status = check_context_with_model(ctx, params, &mdl, n, assumptions.data);

  // Remove temps
  delete_ivector(&assumptions);
  delete_evaluator(&mdl_evaluator);
  delete_model(&mdl);

  return status;
}

/*
 * Check sat with assumptions and build an unsat core
 */
static smt_status_t check_with_assumptions(context_t *ctx, const param_t *params, uint32_t n, const term_t a[], ivector_t *core) {
  ivector_t assumptions;
  smt_status_t status;
  literal_t l;
  uint32_t i;

  // if ctx is already unsat, the core is empty
  if (context_status(ctx) == STATUS_UNSAT) {
    ivector_reset(core);
    return STATUS_UNSAT;
  }

  // If MCSAT use the model solving command
  if (ctx->mcsat) {
    // Copy over to model
    model_t mdl;
    // Map from temporary Boolean variables (labels) to the original assumptions.
    int_hmap_t lmap;

    init_model(&mdl, ctx->terms, true);
    init_int_hmap(&lmap, 0);
    init_ivector(&assumptions, n);

    for (i = 0; i < n; ++ i) {
      // create temporary Boolean label for assumptions
      term_t b = new_uninterpreted_term(ctx->terms, bool_id);
      int_hmap_add(&lmap, b, a[i]);
      yices_assert_formula(ctx, yices_implies(b, a[i]));
      model_map_term(&mdl, b, vtbl_mk_bool(&mdl.vtbl, true));
      ivector_push(&assumptions, b);
    }
    
    // Solve
    status = yices_check_context_with_model(ctx, params, &mdl, n, assumptions.data);

    if (status == STATUS_UNSAT) {
      term_t model_interp = context_get_unsat_model_interpolant(ctx);
      if (model_interp != NULL_TERM) {
	      ivector_t lcore;
        init_ivector(&lcore, 0);
        filter_assumptions_by_term(ctx, model_interp, &assumptions, &lcore);
	      ivector_reset(core);
	      for (i = 0; i < lcore.size; ++ i) {
          int_hmap_pair_t* e = int_hmap_find(&lmap, lcore.data[i]);
          if (e != NULL) {
            // The unsat core from the solver may contain temporary Boolean variables.
            // We use lmap to find the original assumption that corresponds to each
            // temporary variable in the core.
            ivector_push(core, e->val);
            //print_term_full(stderr, ctx->terms, e->val);
            //fflush(stdout);
          }
        }
        delete_ivector(&lcore);
      }
    }

    // Remove temps
    delete_ivector(&assumptions);
    delete_int_hmap(&lmap);
    delete_model(&mdl);

    return status;
  }

  // convert a[0] ... a[n-1] to assumptions
  init_ivector(&assumptions, n);
  for (i=0; i<n; i++) {
    l = context_add_assumption(ctx, a[i]);
    if (l < 0) {
      // error when processing term a[i]
      yices_internalization_error(l);
      status = STATUS_ERROR;
      goto done;
    }
    ivector_push(&assumptions, l);
  }

  status = check_context_with_assumptions(ctx, params, n, assumptions.data);
  if (status == STATUS_UNSAT) {
    context_build_unsat_core(ctx, core);
  }

 done:
  delete_ivector(&assumptions);

  return status;
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
  stats->num_check_sat_assuming = 0;
  stats->num_check_sat_assuming_model = 0;
  stats->num_push = 0;
  stats->num_pop = 0;
  stats->num_get_value = 0;
  stats->num_get_assignment = 0;
  stats->num_get_unsat_core = 0;
  stats->num_get_unsat_assumptions = 0;
}



/*
 * REQUIRED INFO
 */
static const char *yices_name = "Yices";
static const char *yices_authors = "Bruno Dutertre, Dejan Jovanović, Ian A. Mason, Stéphane Graham-Lengrand";
static const char *error_behavior = "immediate-exit";

/*
 * GLOBAL OBJECTS
 */
static bool done;         // set to true on exit
static attr_vtbl_t avtbl; // attribute values

// exported
smt2_globals_t __smt2_globals;



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
 * OUTPUT FUNCTIONS
 */

/*
 * Formatted output: like printf but use __smt2_globals.out
 */
static void __attribute__((format(printf, 1, 2))) print_out(const char *format, ...)  {
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
 * - start_error(l, c) prints '(error "at line l, column c: '
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
static void __attribute__((format(printf, 1, 2))) print_error(const char *format, ...) {
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
    } else if (expected_token == SMT2_COMMAND_EXPECTED && tk == SMT2_TK_SYMBOL) {
      print_out("syntax error: %s is not a command", tkval(lex));
    } else if (expected_token == SMT2_NOT_EXPECTED) {
      print_out("syntax error: '%s' expected", smt2_symbol_to_string(SMT2_SYM_NOT));
    } else if (expected_token == SMT2_LITERAL_EXPECTED) {
      print_out("syntax_error: literal expected");
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
    print_out("%s not supported", what);
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
    unsupported_construct("division by zero");
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

  case CTX_LAMBDAS_NOT_SUPPORTED:
    unsupported_construct("lambdas are");
    break;

  case CTX_SCALAR_NOT_SUPPORTED:
    unsupported_construct("scalar types are");
    break;

  case CTX_TUPLE_NOT_SUPPORTED:
    unsupported_construct("tuples are");
    break;

  case CTX_UTYPE_NOT_SUPPORTED:
    unsupported_construct("uninterpreted sorts are");
    break;

  case CTX_HIGH_ORDER_FUN_NOT_SUPPORTED:
    unsupported_construct("high-order functions are");
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
    print_out("too many variables for the arithmetic solver");
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

  case MCSAT_ERROR_UNSUPPORTED_THEORY:
    print_out("mcsat: unsupported theory");
    break;

  case MCSAT_ERROR_ASSUMPTION_TERM_NOT_SUPPORTED:
    print_out("mcsat: checking with assumptions only supports variables as assumptions");
    break;

  case OUTPUT_ERROR:
    print_out(" IO error");
    break;

  default:
    print_out("BUG detected");
    if (full) close_error();
    freport_bug(__smt2_globals.err, "smt2_commands");
    break;
  }

  if (full) close_error();
}


/*
 * Print an internalization error code: force exit
 */
static void print_internalization_error(int32_t code) {
  yices_internalization_error(code);
  print_yices_error(true);
  done = true;
}

/*
 * Print the error code returned by ef_analyze
 */
static void print_ef_analyze_error(ef_code_t code) {
  assert(code != EF_NO_ERROR);
  print_error("%s", efcode2error[code]);
  done = true;
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
  "Invalid finite field constant",      // TSTACK_INVALID_FFCONSTANT
  "invalid finite field order",         // TSTACK_INVALID_FFCONSTANT
  "incompatible finite field sizes",    // TSTACK_INCOMPATIBLE_FFSIZES
  "incompatible sort in definition",    // TSTACK_TYPE_ERROR_IN_DEFTERM
  "invalid term",                       // TSTACK_STRINGS_ARE_NOT_TERMS
  "variables and values not matching",  // TSTACK_VARIABLES_VALUES_NOT_MATCHING
  "a constant value required",          // TSTACK_NOT_A_CONSTANT,
  "a variable required",                // TSTACK_NOT_A_VARIABLE
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
  NULL,                                 // SMT2_TERM_NOT_INTEGER
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
  "FiniteField",          // MK_FF_TYPE
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
  NULL,                   // MK_BOOL_TO_BV
  NULL,                   // MK_BIT

  "floor",                // MK_FLOOR (not in SMT2)
  "ceil",                 // MK_CEIL (not in SMT2
  "abs",                  // MK_ABS
  "div",                  // MK_IDIV
  "mod",                  // MK_MOD
  "divides",              // MK_DIVIDES (not in SMT2 --> divisible)
  "is_int",               // MK_IS_INT

  "ff.constant",          // MK_FF_CONST
  "ff.add",               // MK_FF_ADD
  "ff.mul",               // MK_FF_MUL

  "build term",           // BUILD_TERM
  "build_type",           // BUILD_TYPE

  "exit",                 // SMT2_EXIT
  "end of file",          // SMT2_SILENT_EXIT
  "get-assertions",       // SMT2_GET_ASSERTIONS
  "get-assignment",       // SMT2_GET_ASSIGNMENT
  "get-proof",            // SMT2_GET_PROOF
  "get-unsat-assumptions",  // SMT2_GET_UNSAT_ASSUMPTIONS
  "get-unsat-core",       // SMT2_GET_UNSAT_CORE
  "get-unsat-model-interpolant", // SMT2_GET_UNSAT_MODEL_INTERPOLANT
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
  "check-sat-assuming",   // SMT2_CHECK_SAT_ASSUMING,
  "check-sat-assuming-model", // SMT2_CHECK_SAT_ASSUMING_MODEL
  "declare-sort",         // SMT2_DECLARE_SORT
  "define-sort",          // SMT2_DEFINE_SORT
  "declare-fun",          // SMT2_DECLARE_FUN
  "define-fun",           // SMT2_DEFINE_FUN
  "get-model",            // SMT2_GET_MODEL
  "echo",                 // SMT2_ECHO
  "reset-assertions",     // SMT2_RESET_ASSERTIONS
  "reset",                // SMT2_RESET_ALL
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

  // more arithmetic stuff
  "to_real",              // SMT2_MK_TO_REAL
  "div",                  // SMT2_MK_DIV
  "mod",                  // SMT2_MK_MOD
  "abs",                  // SMT2_MK_ABS
  "to_int",               // SMT2_MK_TO_INT
  "is_int",               // SMT2_MK_IS_INT
  "divisible",            // SMT2_MK_DIVISIBLE
};



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
  case TSTACK_NOT_A_CONSTANT:
  case TSTACK_NOT_A_VARIABLE:
  case TSTACK_VARIABLES_VALUES_NOT_MATCHING:
  case TSTACK_ARITH_ERROR:
  case TSTACK_DIVIDE_BY_ZERO:
  case TSTACK_NON_CONSTANT_DIVISOR:
  case TSTACK_INCOMPATIBLE_BVSIZES:
  case TSTACK_INCOMPATIBLE_FFSIZES:
  case TSTACK_INVALID_FFSIZE:
  case TSTACK_INVALID_BVCONSTANT:
  case TSTACK_INVALID_FFCONSTANT:
  case TSTACK_BVARITH_ERROR:
  case TSTACK_BVLOGIC_ERROR:
  case TSTACK_TYPE_ERROR_IN_DEFTERM:
  case SMT2_MISSING_NAME:
  case SMT2_MISSING_PATTERN:
  case SMT2_TYPE_ERROR_IN_QUAL:
  case SMT2_QUAL_NOT_IMPLEMENTED:
  case SMT2_INVALID_IDX_BV:
  case SMT2_NAMED_TERM_NOT_GROUND:
  case SMT2_NAMED_SYMBOL_REUSED:
    print_out("%s", exception_string[exception]);
    break;

  case SMT2_TERM_NOT_INTEGER:
    print_out("invalid argument in %s: not an integer",  opcode_string[tstack->error_op]);
    break;

  case TSTACK_STRINGS_ARE_NOT_TERMS:
    print_out("%s: \"%s\"", exception_string[exception], tstack->error_string);
    break;

  case TSTACK_YICES_ERROR:
    // TODO: extract more information from yices_error_report();
    print_out("in %s: ", opcode_string[tstack->error_op]);
    print_yices_error(false);
    break;

  case TSTACK_NO_ERROR:
  case TSTACK_INTERNAL_ERROR:
  case TSTACK_DUPLICATE_SCALAR_NAME:
  case TSTACK_INVALID_OP:
  case TSTACK_NEGATIVE_EXPONENT:
  default:
    print_out("FATAL ERROR");
    close_error();
    freport_bug(__smt2_globals.err, "smt2_commands");
    break;
  }

  close_error();
  done = true;
}


/*
 * Bug report: unexpected status
 */
static void __attribute__((noreturn)) bad_status_bug(FILE *f) {
  print_error("Internal error: unexpected context status");
  flush_out();
  freport_bug(f, "Internal error: unexpected context status");
}



/*
 * PRINT STATUS AND STATISTICS
 */
static void show_status(smt_status_t status) {
  print_out("%s\n", status2string[status]);
  flush_out();
}


/*
 * Status after check_with_assumptions or check: print an error if the
 * status is not SAT/UNSAT/UNKNOWN/INTERRUPTED
 */
static void report_status(smt2_globals_t *g, smt_status_t status) {
  switch (status) {
  case STATUS_UNKNOWN:
  case STATUS_UNSAT:
  case YICES_STATUS_INTERRUPTED:
    show_status(status);
    break;

  case STATUS_SAT:
    show_status(status);
    if (g->dump_models) {
      smt2_get_model();
    }
    break;

  case STATUS_ERROR:
    print_yices_error(true);
    break;

  default:
    bad_status_bug(g->err);
    break;
  }
}


/*
 * Print the efsolver status. Print an error if the status
 * is not SAT/UNSAT/UNKNOWN/INTERRUPTED.
 */
static void report_ef_status(smt2_globals_t *g, ef_client_t *efc) {
  ef_status_t stat;
  int32_t error;
  ef_solver_t *efsolver;

  efsolver = efc->efsolver;

  assert(efsolver != NULL && efc->efdone);

  stat = efsolver->status;
  error = efsolver->error_code;

  switch (stat) {
  case EF_STATUS_SAT:
  case EF_STATUS_UNKNOWN:
  case EF_STATUS_UNSAT:
  case EF_STATUS_INTERRUPTED:
    trace_printf(g->tracer, 3, "(exist/forall solver: %"PRIu32" iterations)\n", efsolver->iters);
    print_out("%s\n", ef_status2string[stat]);
    flush_out();
    break;

  case EF_STATUS_SUBST_ERROR:
    if (error == -1) {
      print_error("the exist/forall solver failed: degree overflow in substitution");
    } else {
      assert(error == -2);
      freport_bug(g->err, "the exist/forall solver failed: substitution error");
    }
    break;

  case EF_STATUS_ASSERT_ERROR:
    assert(error < 0);
    print_internalization_error(error);
    break;

  case EF_STATUS_PROJECTION_ERROR:
    if (error == PROJ_ERROR_NON_LINEAR) {
      print_error("the exists/forall solver failed: non-linear arithmetic is not supported");
    } else if (error == PROJ_ERROR_UNSUPPORTED_ARITH_TERM ||
	       error == PROJ_ERROR_BAD_ARITH_LITERAL ||
	       error == PROJ_ERROR_BAD_PRESBURGER_LITERAL) {
      print_error("the exists/forall solver failed: unsupported term");
    } else {
      freport_bug(g->err, "the exists/forall solver failed: projection error");
    }
    break;

  case EF_STATUS_MDL_ERROR:
  case EF_STATUS_IMPLICANT_ERROR:
  case EF_STATUS_TVAL_ERROR:
  case EF_STATUS_CHECK_ERROR:
  case EF_STATUS_ERROR:
  case EF_STATUS_IDLE:
  case EF_STATUS_SEARCHING:
    freport_bug(g->err, "the exists/forall solver failed: unexpected status: %s\n", ef_status2string[stat]);
    break;
  }
}




/*
 * Statistics about each solvers.
 * This may be called from a signal handler so we use the "simple_printf.h" functions.
 * All the functions print to file fd using print_buffer_b for formatting.
 */
static void print_string_and_uint32(int fd, print_buffer_t *b, const char *s, uint32_t x) {
  reset_print_buffer(b);
  print_buffer_append_string(b, s);
  print_buffer_append_uint32(b, x);
  print_buffer_append_char(b, '\n');
  (void) write_buffer(fd, b);
}

static void print_string_and_uint64(int fd, print_buffer_t *b, const char *s, uint64_t x) {
  reset_print_buffer(b);
  print_buffer_append_string(b, s);
  print_buffer_append_uint64(b, x);
  print_buffer_append_char(b, '\n');
  (void) write_buffer(fd, b);
}

static void print_string_and_float(int fd, print_buffer_t *b, const char *s, double x) {
  reset_print_buffer(b);
  print_buffer_append_string(b, s);
  print_buffer_append_float(b, x, 3); // 3 digits after the decimal point
  print_buffer_append_char(b, '\n');
  (void) write_buffer(fd, b);
}

static void print_char_and_newline(int fd, print_buffer_t *b, char c) {
  reset_print_buffer(b);
  print_buffer_append_char(b, c);
  print_buffer_append_char(b, '\n');
  (void) write_buffer(fd, b);
}

static void show_core_stats(int fd, print_buffer_t *b, smt_core_t *core) {
  print_string_and_uint32(fd, b, " :boolean-variables ", num_vars(core));
  print_string_and_uint32(fd, b, " :atoms ", num_atoms(core));
  print_string_and_uint32(fd, b, " :clauses ", num_clauses(core));
  print_string_and_uint32(fd, b, " :restarts ", num_restarts(core));
  print_string_and_uint32(fd, b, " :clause-db-reduce ", num_reduce_calls(core));
  print_string_and_uint32(fd, b, " :clause-db-simplify ", num_simplify_calls(core));
  print_string_and_uint64(fd, b, " :decisions ", num_decisions(core));
  print_string_and_uint64(fd, b, " :conflicts ", num_conflicts(core));
  print_string_and_uint32(fd, b, " :theory-conflicts ", num_theory_conflicts(core));
  print_string_and_uint64(fd, b, " :boolean-propagations ", num_propagations(core));
  print_string_and_uint32(fd, b, " :theory-propagations ", num_theory_propagations(core));
}

static void show_egraph_stats(int fd, print_buffer_t *b, egraph_t *egraph) {
  print_string_and_uint32(fd, b, " :egraph-terms ", egraph_num_terms(egraph));
  print_string_and_uint32(fd, b, " :egraph-atoms ", egraph_num_atoms(egraph));
  print_string_and_uint32(fd, b, " :egraph-conflicts ", egraph_num_conflicts(egraph));
  print_string_and_uint32(fd, b, " :egraph-ackermann-lemmas ", egraph_all_ackermann(egraph));
  print_string_and_uint32(fd, b, " :egraph-final-checks ", egraph_num_final_checks(egraph));
  print_string_and_uint32(fd, b, " :egraph-interface-lemmas ", egraph_num_interface_eqs(egraph));
}

static void show_funsolver_stats(int fd, print_buffer_t *b, fun_solver_t *solver) {
  print_string_and_uint32(fd, b, " :array-vars ", fun_solver_num_vars(solver));
  print_string_and_uint32(fd, b, " :array-edges ", fun_solver_num_edges(solver));
  print_string_and_uint32(fd, b, " :array-update1-axioms ", fun_solver_num_update1_axioms(solver));
  print_string_and_uint32(fd, b, " :array-update2-axioms ", fun_solver_num_update2_axioms(solver));
  print_string_and_uint32(fd, b, " :array-extensionality-axioms ", fun_solver_num_extensionality_axioms(solver));
}

static void show_quantsolver_stats(int fd, print_buffer_t *b, quant_solver_t *solver) {
  print_string_and_uint32(fd, b, " :ematch-quantifiers ", quant_solver_num_quantifiers(solver));
  print_string_and_uint32(fd, b, " :ematch-patterns ", quant_solver_num_patterns(solver));
  print_string_and_uint32(fd, b, " :ematch-instances ", quant_solver_num_instances(solver));
  print_string_and_uint32(fd, b, " :ematch-rounds ", solver->stats.num_rounds);
  print_string_and_uint32(fd, b, " :ematch-searches ", solver->stats.num_search);
  print_string_and_uint32(fd, b, " :ematch-trial-fdepth ", solver->em.exec.fdepth);
  print_string_and_uint32(fd, b, " :ematch-trial-vdepth ", solver->em.exec.vdepth);
  print_string_and_uint32(fd, b, " :ematch-cnstr-epsilon ", solver->cnstr_learner.learner.epsilon);
  print_string_and_float(fd, b, " :ematch-cnstr-alpha ", solver->cnstr_learner.learner.alpha);
  print_string_and_uint32(fd, b, " :ematch-term-epsilon ", solver->term_learner.learner.epsilon);
  print_string_and_float(fd, b, " :ematch-term-alpha ", solver->term_learner.learner.alpha);
}

static void show_simplex_stats(int fd, print_buffer_t *b, simplex_solver_t *solver) {
  simplex_collect_statistics(solver);
  print_string_and_uint32(fd, b, " :simplex-init-vars ", simplex_num_init_vars(solver));
  print_string_and_uint32(fd, b, " :simplex-init-rows ", simplex_num_init_rows(solver));
  print_string_and_uint32(fd, b, " :simplex-init-atoms ", simplex_num_init_atoms(solver));
  print_string_and_uint32(fd, b, " :simplex-vars ", simplex_num_vars(solver));
  print_string_and_uint32(fd, b, " :simplex-rows ", simplex_num_rows(solver));
  print_string_and_uint32(fd, b, " :simplex-atoms ", simplex_num_atoms(solver));
  print_string_and_uint32(fd, b, " :simplex-pivots ", simplex_num_pivots(solver));
  print_string_and_uint32(fd, b, " :simplex-conflicts ", simplex_num_conflicts(solver));
  print_string_and_uint32(fd, b, " :simplex-interface-lemmas ", simplex_num_interface_lemmas(solver));
  if (simplex_num_make_integer_feasible(solver) > 0 ||
      simplex_num_dioph_checks(solver) > 0) {
    print_string_and_uint32(fd, b, " :simplex-integer-vars ", simplex_num_integer_vars(solver));
    print_string_and_uint32(fd, b, " :simplex-branch-and-bound ", simplex_num_branch_and_bound(solver));
    print_string_and_uint32(fd, b, " :simplex-gomory-cuts ", simplex_num_gomory_cuts(solver));
    // bound strenthening
    print_string_and_uint32(fd, b, " :simplex-bound-conflicts ", simplex_num_bound_conflicts(solver));
    print_string_and_uint32(fd, b, " :simplex-bound-recheck-conflicts ", simplex_num_bound_recheck_conflicts(solver));
    // integrality test
    print_string_and_uint32(fd, b, " :simplex-itest-conflicts ", simplex_num_itest_conflicts(solver));
    print_string_and_uint32(fd, b, " :simplex-itest-bound-conflicts ", simplex_num_itest_bound_conflicts(solver));
    print_string_and_uint32(fd, b, " :simplex-itest-recheck-conflicts ", simplex_num_itest_bound_conflicts(solver));
    // diophantine solver
    print_string_and_uint32(fd, b, " :simplex-gcd-conflicts ", simplex_num_dioph_gcd_conflicts(solver));
    print_string_and_uint32(fd, b, " :simplex-dioph-checks ", simplex_num_dioph_checks(solver));
    print_string_and_uint32(fd, b, " :simplex-dioph-conflicts ", simplex_num_dioph_conflicts(solver));
    print_string_and_uint32(fd, b, " :simplex-dioph-bound-conflicts ", simplex_num_dioph_bound_conflicts(solver));
    print_string_and_uint32(fd, b, " :simplex-dioph-recheck-conflicts ", simplex_num_dioph_recheck_conflicts(solver));
  }
}

static void show_bvsolver_stats(int fd, print_buffer_t *b, bv_solver_t *solver) {
  print_string_and_uint32(fd, b, " :bvsolver-vars ", bv_solver_num_vars(solver));
  print_string_and_uint32(fd, b, " :bvsolver-atoms ", bv_solver_num_atoms(solver));
  print_string_and_uint32(fd, b, " :bvsolver-equiv-lemmas ", bv_solver_equiv_lemmas(solver));
  print_string_and_uint32(fd, b, " :bvsolver-interface-lemmas ", bv_solver_interface_lemmas(solver));
}

static void show_idl_fw_stats(int fd, print_buffer_t *b, idl_solver_t *solver) {
  print_string_and_uint32(fd, b, " :idl-solver-vars ", idl_num_vars(solver));
  print_string_and_uint32(fd, b, " :idl-solver-atoms ", idl_num_atoms(solver));
}

static void show_rdl_fw_stats(int fd, print_buffer_t *b, rdl_solver_t *solver) {
  print_string_and_uint32(fd, b, " :rdl-solver-vars ", rdl_num_vars(solver));
  print_string_and_uint32(fd, b, " :rdl-solver-atoms ", rdl_num_atoms(solver));
}


/*
 * Context statistics
 */
static void show_ctx_stats(int fd, print_buffer_t *b, context_t *ctx) {
  assert(ctx->core != NULL);
  show_core_stats(fd, b, ctx->core);

  if (context_has_egraph(ctx)) {
    show_egraph_stats(fd, b, ctx->egraph);
  }

  if (context_has_fun_solver(ctx)) {
    show_funsolver_stats(fd, b, ctx->fun_solver);
  }

  if (context_has_quant_solver(ctx)) {
    show_quantsolver_stats(fd, b, ctx->quant_solver);
  }

  if (context_has_arith_solver(ctx)) {
    if (context_has_simplex_solver(ctx)) {
      show_simplex_stats(fd, b, ctx->arith_solver);
    } else if (context_has_idl_solver(ctx)) {
      show_idl_fw_stats(fd, b, ctx->arith_solver);
    } else {
      assert(context_has_rdl_solver(ctx));
      show_rdl_fw_stats(fd, b, ctx->arith_solver);
    }
  }

  if (context_has_bv_solver(ctx)) {
    show_bvsolver_stats(fd, b, ctx->bv_solver);
  }

  if (ctx->mcsat != NULL) {
    mcsat_show_stats_fd(ctx->mcsat, fd);
  }
}

/*
 *
 */
static void show_ef_stats(int fd, print_buffer_t *b, ef_client_t *efc) {
  print_string_and_uint32(fd, b, " :quantifiers ", efc->efprob->num_cnstr);
  print_string_and_uint32(fd, b, " :mbqi-models ", efc->efsolver->num_models);
  print_string_and_uint32(fd, b, " :mbqi-cex ", efc->efsolver->numiters);
  print_string_and_uint32(fd, b, " :mbqi-instances ", efc->efsolver->numlearnt);
}


/*
 * Global state
 */
static void show_statistics(smt2_globals_t *g) {
  print_buffer_t buffer;
  double time, mem;
  context_t *ctx;

  time = get_cpu_time();
  mem = mem_size() / (1024*1024);

  print_char_and_newline(g->out_fd, &buffer, '(');
  print_string_and_uint32(g->out_fd, &buffer, " :num-terms ", yices_num_terms());
  print_string_and_uint32(g->out_fd, &buffer, " :num-types ", yices_num_types());
  print_string_and_float(g->out_fd, &buffer, " :total-run-time ", time);
  if (mem > 0) {
    print_string_and_float(g->out_fd, &buffer, " :mem-usage ", mem);
  }
  if (g->efmode && g->ef_client.efsolver != NULL) {
    ctx = g->ef_client.efsolver->exists_context;
    if (ctx != NULL) {
      show_ctx_stats(g->out_fd, &buffer, ctx);
    }
    show_ef_stats(g->out_fd, &buffer, &g->ef_client);
  } else {
    ctx = g->ctx;
    if (ctx != NULL) {
      show_ctx_stats(g->out_fd, &buffer, ctx);
    }
  }

  print_char_and_newline(g->out_fd, &buffer, ')');
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
static void init_pretty_printer(smt2_pp_t *printer, smt2_globals_t *g) {
  init_smt2_pp(printer, g->out, &g->pp_area, PP_VMODE, g->bvconst_in_decimal);
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
 * For (set-info :smt-lib-version X.Y)
 * - check whether v is either 2.0 or 2.5 or 2.6
 * - return false if it's not
 * - return true if it is
 *
 * - set *version to 100 * v (i.e., 2.5 --> 2500)
 */
static bool aval_is_known_version(attr_vtbl_t *avtbl, aval_t v, uint32_t *version) {
  rational_t aux;
  bool ok;

  ok = false;
  if (v >= 0 && aval_tag(avtbl, v) == ATTR_RATIONAL) {
    q_init(&aux);
    q_set(&aux, aval_rational(avtbl, v));
    if (q_cmp_int32(&aux, 2, 1) == 0) {
      // version 2.0
      *version = 2000;
      ok = true;
    } else if (q_cmp_int32(&aux, 5, 2) == 0) {
      // version 2.5
      *version = 2500;
      ok = true;
    } else if (q_cmp_int32(&aux, 13, 5) == 0) {
      // version 2.6
      *version = 2600;
      ok = true;
    }
    q_clear(&aux);
  }

  return ok;
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
    } else if (q_get64(&aux, &x) && x <= (int64_t) UINT32_MAX) {
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
    g->out_fd = fileno(f);
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
    g->err_fd = fileno(f);
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
      print_error("integer overflow: %s must be at most %"PRIu32, name, UINT32_MAX);
    }
  } else {
    print_error("option %s requires an integer value", name);
  }
  q_clear(&aux);
}


/*
 * Options: produce-unsat-cores and produce-unsat-assumptions.
 * It's not clear what to do if both were true. So we make
 * sure only one of them is true,
 */
static void set_unsat_core_option(smt2_globals_t *g, const char *name, aval_t value) {
  bool flag;

  if (aval_is_boolean(g->avtbl, value, &flag)) {
    if (flag && g->produce_unsat_assumptions) {
      print_error("can't have both :produce-unsat-cores and :produce-unsat-assumptions true");
    } else {
      g->produce_unsat_cores = flag;
      // Set model_interpolation if context is MCSAT or will use MCSAT architecture
      if (g->mcsat || (g->logic_code != SMT_UNKNOWN && arch_for_logic(g->logic_code) == CTX_ARCH_MCSAT)) {
        g->mcsat_options.model_interpolation = true;
      }
      report_success();
    }
  } else {
    print_error("option %s requires a Boolean value", name);
  }
}

static void set_unsat_assumption_option(smt2_globals_t *g, const char *name, aval_t value) {
  bool flag;

  if (aval_is_boolean(g->avtbl, value, &flag)) {
    if (flag && g->produce_unsat_cores) {
      print_error("can't have both :produce-unsat-cores and :produce-unsat-assumptions true");
    } else {
      g->produce_unsat_assumptions = flag;
      // Set model_interpolation if context is MCSAT or will use MCSAT architecture
      if (g->mcsat || (g->logic_code != SMT_UNKNOWN && arch_for_logic(g->logic_code) == CTX_ARCH_MCSAT)) {
        g->mcsat_options.model_interpolation = true;
      }
      report_success();
    }
  } else {
    print_error("option %s requires a Boolean value", name);
  }
}

static void set_unsat_model_interpolants_option(smt2_globals_t *g, const char *name, aval_t value) {
  bool flag;

  if (aval_is_boolean(g->avtbl, value, &flag)) {
    g->produce_unsat_model_interpolants = flag;
    g->mcsat_options.model_interpolation = true;
    report_success();
  } else {
    print_error("option %s requires a Boolean value", name);
  }
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

static void print_kw_uint64_pair(const char *keyword, uint64_t value) {
  print_out("(%s %"PRIu64")\n", keyword, value);
}

static const char * const string_bool[2] = { "false", "true" };

#if 0
// not used

static void print_kw_boolean_pair(const char *keyword, bool value) {
  print_kw_symbol_pair(keyword, string_bool[value]);
}

#endif

/*
 * Print value
 */
static void print_string_value(const char *value) {
  print_out("\"%s\"\n", value);
}

static void print_symbol_value(const char *value) {
  print_out("%s\n", value);
}

static void print_boolean_value(bool value) {
  print_symbol_value(string_bool[value]);
}

static void print_int32_value(uint32_t value) {
  print_out("%"PRIi32"\n", value);
}

static void print_uint32_value(uint32_t value) {
  print_out("%"PRIu32"\n", value);
}

static void print_float_value(double value) {
  if (value < 1.0) {
    print_out("%.4f\n", value);
  } else {
    print_out("%.2f\n", value);
  }
}

static void print_terms_value(smt2_globals_t *g, const ivector_t* order) {
  smt2_pp_t printer;

  init_pretty_printer(&printer, g);
  pp_open_block(&printer.pp, PP_OPEN_VPAR); // open '('
  if (order != NULL) {
    for (uint32_t i = 0; i < order->size; ++ i) {
      pp_term_full(&printer.pp, __yices_globals.terms, order->data[i]);
    }
  } else {
    pp_string(&printer.pp,"null");
  }
  pp_close_block(&printer.pp, true); // close ')'
  delete_smt2_pp(&printer, true);
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
    freport_bug(g->err, "smt2_commands: attribute deleted");
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
 * ASSUMPTIONS AND NAMED ASSERTIONS
 */

/*
 * Allocate an assumption structure and store all named assertions in it.
 */
static assumptions_and_core_t *collect_named_assertions(smt2_globals_t *g) {
  assumptions_and_core_t *a;

  a = new_assumptions(__yices_globals.terms);
  collect_assumptions_from_stack(a, &g->named_asserts);
  return a;
}


/*
 * Allocate an assumption structure and store assumptions in it
 * - return NULL and print an error is any symbol is undefined or not Boolean
 */
static assumptions_and_core_t *collect_named_assumptions(uint32_t n, const signed_symbol_t *a) {
  assumptions_and_core_t *tmp;
  int32_t code;
  uint32_t index;

  tmp = new_assumptions(__yices_globals.terms);
  code = collect_assumptions_from_signed_symbols(tmp, n, a, &index);
  if (code < 0) {
    // failed: index = the bad term
    assert(0 <= index && index < n);
    if (code == -1) {
      print_error("undefined term %s", a[index].name);
    } else {
      print_error("term %s is not Boolean", a[index].name);
    }
    free_assumptions(tmp);
    tmp = NULL;
  }

  return tmp;
}

/*
 * CONTEXT INITIALIZATION
 */

/*
 * Check whether we can set the context in one-check mode
 * - we can if g->benchmark is true
 *   and g->produce_unsat_cores and g->produce_unsat_assumptions
 *   are both false.
 */
static inline bool one_check_mode(smt2_globals_t *g) {
  return g->benchmark_mode && !g->produce_unsat_cores &&
    !g->produce_unsat_assumptions;
}

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
  assert(!g->efmode);

  // default: assume g->benchmark_mode is false
  logic = g->logic_code;
  mode = CTX_MODE_PUSHPOP;
  if (g->timeout > 0) {
    mode = CTX_MODE_INTERACTIVE;
  }
  arch = arch_for_logic(logic);
  iflag = iflag_for_logic(logic);
  qflag = qflag_for_logic(logic);

  if (g->mcsat) {
    // force MCSAT independent of the logic
    arch = CTX_ARCH_MCSAT;
  } else if (one_check_mode(g)) {
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

  if (arch == CTX_ARCH_MCSAT) {
    iflag = false;
    qflag = false;
  }

  g->ctx = yices_create_context(logic, arch, mode, iflag, qflag);
  assert(g->ctx != NULL);
  if (g->verbosity > 0 || g->tracer != NULL) {
    context_set_trace(g->ctx, get_tracer(g));
  }

  // Set the mcsat options
  g->ctx->mcsat_options = g->mcsat_options;
  ivector_copy(&g->ctx->mcsat_var_order, g->var_order.data, g->var_order.size);

  /*
   * TODO: override the default context options based on
   * ctx_parameters.  I don't want to do it now (2015/07/22). If we
   * make a mistake, we could get a major performance loss.
   */
}


/*
 * Initialize the search parameters
 * - this must be done after the context is created
 * - if the architecture is AUTO_RDL or AUTO_IDL,
 *   this must be called after the assertions
 */
static void init_search_parameters(smt2_globals_t *g) {
  assert(g->ctx != NULL);
  yices_default_params_for_context(g->ctx, &g->parameters);
}



/*
 * CHECK SAT WITH TIMEOUT
 */

/*
 * Timeout handler: call stop_search when triggered
 * - data = pointer to the smt2_global structure
 */
static void timeout_handler(void *data) {
  smt2_globals_t *g;

#ifndef THREAD_SAFE
  assert(data == &__smt2_globals);
#else
  /* In the multi-threaded case there are multiple copies of the
     global data. */
#endif /* THREAD_SAFE */
  
  g = data;
  if (g->efmode && g->ef_client.efsolver != NULL && g->ef_client.efsolver->status == EF_STATUS_SEARCHING) {
    ef_solver_stop_search(g->ef_client.efsolver);
  } else if (g->ctx != NULL && context_status(g->ctx) == STATUS_SEARCHING) {
    context_stop_search(g->ctx);
  }
}

/*
 * Call check_context with the given search parameters.
 * - if g->timeout is positive, set a timeout first
 */
static smt_status_t check_sat_with_timeout(smt2_globals_t *g, const param_t *params) {
  smt_status_t stat;

  if (g->timeout == 0) {
    // no timeout
    return check_context(g->ctx, params);
  }

  /*
   * We call init_timeout only now because the internal timeout
   * consumes resources even if it's never used.
   */
  if (! g->to) {
    g->to = init_timeout();
  }
  g->interrupted = false;
  start_timeout(g->to, g->timeout, timeout_handler, g);
  stat = check_context(g->ctx, params);
  clear_timeout(g->to);

  /*
   * Attempt to cleanly recover from interrupt
   */
  if (stat == YICES_STATUS_INTERRUPTED) {
    trace_printf(g->tracer, 2, "(check-sat: interrupted)\n");
    g->interrupted = true;
    if (context_get_mode(g->ctx) == CTX_MODE_INTERACTIVE) {
      context_cleanup(g->ctx);
      assert(context_status(g->ctx) == STATUS_IDLE);
    }
    // we don't want to report "interrupted" that's not SMT2 compliant
    stat = STATUS_UNKNOWN;
  }

  return stat;
}


/*
 * Check with assumptions:
 * - params = search parameters
 * - a = assumption data structure to use
 */
static smt_status_t check_sat_with_assumptions(smt2_globals_t *g, const param_t *params, assumptions_and_core_t *a) {
  smt_status_t stat;

  if (g->timeout == 0) {
    // no timeout
    stat = check_with_assumptions(g->ctx, params, a->assumptions.size, a->assumptions.data, &a->core);
    a->status = stat;
    return stat;
  }

  /*
   * We call init_timeout only now because the internal timeout
   * consumes resources even if it's never used.
   */
  if (! g->to) {
    g->to = init_timeout();
  }
  g->interrupted = false;
  start_timeout(g->to, g->timeout, timeout_handler, g);
  stat = check_with_assumptions(g->ctx, params, a->assumptions.size, a->assumptions.data, &a->core);
  a->status = stat;
  clear_timeout(g->to);

  /*
   * Attempt to cleanly recover from interrupt
   */
  if (stat == YICES_STATUS_INTERRUPTED) {
    trace_printf(g->tracer, 2, "(check-sat-assuming: interrupted)\n");
    g->interrupted = true;
    if (context_get_mode(g->ctx) == CTX_MODE_INTERACTIVE) {
      context_cleanup(g->ctx);
      assert(context_status(g->ctx) == STATUS_IDLE);
    }
    // we don't want to report "interrupted" that's not SMT2 compliant
    stat = STATUS_UNKNOWN;
  }

  return stat;
}

/*
 * Check with model assumptions:
 * - params = search parameters
 * - n = size of model
 * - vars = the variables
 * - values = the values
 */
static smt_status_t check_sat_with_model(smt2_globals_t *g, const param_t *params, uint32_t n, const term_t vars[], const term_t values[]) {
  smt_status_t stat;

  if (g->timeout == 0) {
    // no timeout
    stat = check_with_model(g->ctx, params, n, vars, values);
    g->check_with_model_status = stat;
    return stat;
  }

  /*
   * We call init_timeout only now because the internal timeout
   * consumes resources even if it's never used.
   */
  if (! g->to) {
    g->to = init_timeout();
  }
  g->interrupted = false;
  start_timeout(g->to, g->timeout, timeout_handler, g);
  stat = check_with_model(g->ctx, params, n, vars, values);
  clear_timeout(g->to);

  /*
   * Attempt to cleanly recover from interrupt
   */
  if (stat == YICES_STATUS_INTERRUPTED) {
    trace_printf(g->tracer, 2, "(check-sat-assuming-model: interrupted)\n");
    g->interrupted = true;
    if (context_get_mode(g->ctx) == CTX_MODE_INTERACTIVE) {
      context_cleanup(g->ctx);
      assert(context_status(g->ctx) == STATUS_IDLE);
    }
    // we don't want to report "interrupted" that's not SMT2 compliant
    stat = STATUS_UNKNOWN;
  }

  g->check_with_model_status = stat;

  return stat;
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
    case ARITH_FF_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      result = false;
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
    case ARITH_IS_INT_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
      result = needs_egraph(seen, arith_atom_arg(terms, t));
      break;

    case ARITH_ROOT_ATOM:
      result = needs_egraph(seen, arith_root_atom_desc(terms, t)->p);
      break;

    case ARITH_FF_EQ_ATOM:
      result = needs_egraph(seen, arith_ff_eq_arg(terms, t));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case EQ_TERM:
    case DISTINCT_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    case ARITH_DIVIDES_ATOM:
    case ARITH_FF_BINEQ_ATOM:
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

    case ARITH_FF_POLY:
      result = poly_needs_egraph(seen, finitefield_poly_term_desc(terms, t));
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
static bool _o_has_uf(term_t *a, uint32_t n) {
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
static bool has_uf(term_t *a, uint32_t n) {
  MT_PROTECT(bool, __yices_globals.lock, _o_has_uf(a, n));
}

/*
 * Add a assertion t to g->assertions
 * - do nothing if t is true
 * - if t is false, set g->trivially_unsat to true
 */
static void add_delayed_assertion(smt2_globals_t *g, term_t t) {
  if (t != true_term) {
#if 0
    printf("adding assertion: ");
    yices_pp_term(stdout, t, 120, 1, 0);
#endif

    ivector_push(&g->assertions, t);
    if (t == false_term) {
      g->trivially_unsat = true;
    }
  }
}


/*
 * Check satisfiability of all assertions
 */
static void check_delayed_assertions(smt2_globals_t *g, bool report) {
  int32_t code;
  smt_status_t status;
  model_t *model;

  // set frozen to true to disallow more assertions
  g->frozen = true;

  if (g->trivially_unsat) {
    trace_printf(g->tracer, 3, "(check-sat: trivially unsat)\n");
    if (report)
      report_status(g, STATUS_UNSAT);
  } else if (trivially_true_assertions(g->assertions.data, g->assertions.size, &model)) {
    trace_printf(g->tracer, 3, "(check-sat: trivially true)\n");
    g->trivially_sat = true;
    g->model = model;
    if (report)
      report_status(g, STATUS_SAT);
  } else {
    /*
     * check for mislabeled benchmarks: some benchmarks
     * marked as QF_UFIDL do not require the Egraph (should be QF_IDL)
     */
    if (g->benchmark_mode && g->logic_code == QF_UFIDL &&
        !has_uf(g->assertions.data, g->assertions.size)) {
      trace_printf(g->tracer, 2, "(Warning: switching logic to QF_IDL)\n");
      g->logic_code = QF_IDL;
    }
    init_smt2_context(g);

    if (g->export_to_dimacs) {
      /*
       * Bitblast and export in DIMACS format.
       */
      code = export_delayed_assertions(g->ctx, g->assertions.size, g->assertions.data, g->dimacs_file);
      if (code < 0) {
        print_yices_error(true);
        done = true;
        return;
      }

    } else {
      /*
       * Assert formulas
       */
      code = yices_assert_formulas(g->ctx, g->assertions.size, g->assertions.data);
      if (code < 0) {
        // error during assertion processing
        print_yices_error(true);
        done = true;
        return;
      }

      if (g->delegate != NULL && g->logic_code == QF_BV) {
        /*
         * Special case: QF_BV with delegate
         */
        if (g->dimacs_file == NULL) {
          status = check_with_delegate(g->ctx, g->delegate, g->verbosity);
        } else {
          code = process_then_export_to_dimacs(g->ctx, g->dimacs_file, &status);
          if (code < 0) {
            perror(g->dimacs_file);
            exit(YICES_EXIT_SYSTEM_ERROR);
          }
          if (status == STATUS_UNKNOWN) {
            // don't print anything
            return;
          }
        }
      } else {
        /*
         * Regular check
         */
        init_search_parameters(g);
        if (g->random_seed != 0) {
          g->parameters.random_seed = g->random_seed;
        }
        status = check_sat_with_timeout(g, &g->parameters);
      }

      if (report)
        report_status(g, status);
    }
  }
}


#if 0
/*
 * FOR TESTING/DEBUGGING: PRINT ALL DELAYED ASSERTIONS
 */
#include "io/term_printer.h"

static void show_delayed_assertions(smt2_globals_t *g) {
  smt2_pp_t printer;
  term_t *v;
  uint32_t i, n;

  if (g->benchmark_mode) {
    fprintf(g->out, "--- All terms ---\n");
    pp_term_table(g->out, __yices_globals.terms);
    fprintf(g->out, "\n");

    fprintf(g->out, "--- Assertions --\n");
    v = g->assertions.data;
    n = g->assertions.size;

    init_pretty_printer(&printer, g);
    for (i=0; i<n; i++) {
      pp_term(&printer.pp, __yices_globals.terms, v[i]);
      flush_smt2_pp(&printer);
    }
    delete_smt2_pp(&printer, true);
  }
}
#endif



#if 0
/*
 * For debugging: check that the unsat core is unsat!
 */
static void validate_unsat_core(smt2_globals_t *g) {
  context_t *saved_context;
  assumptions_and_core_t *a;
  ivector_t all;
  int32_t code;
  smt_status_t status;

  if (g->unsat_core->status == STATUS_UNSAT) {
    saved_context = g->ctx;
    g->ctx = NULL;
    init_smt2_context(g);

    a = g->unsat_core;

    init_ivector(&all, 100);
    ivector_add(&all, g->assertions.data, g->assertions.size);
    ivector_add(&all, a->core.data, a->core.size);
    code = yices_assert_formulas(g->ctx, all.size, all.data);
    if (code < 0) {
      printf("**** BUG: INVALID UNSAT CORE: BAD TERMS ****\n");
      fflush(stdout);
    } else {
      status = check_context(g->ctx, &g->parameters);
      if (status != STATUS_UNSAT) {
        printf("**** BUG: INVALID UNSAT CORE ****\n");
        fflush(stdout);
      }
    }
    delete_ivector(&all);
    yices_free_context(g->ctx);
    g->ctx = saved_context;
  }
}
#endif

/*
 * Check and build unsat core for the delayed assertions
 */
static void delayed_assertions_unsat_core(smt2_globals_t *g) {
  int32_t code;
  smt_status_t status;

  // disallow more assertions
  g->frozen = true;

  assert(g->unsat_core == NULL);
  g->unsat_core = collect_named_assertions(g);
  if (g->trivially_unsat) {
    // the core is empty
    g->unsat_core->status = STATUS_UNSAT;
    report_status(g, STATUS_UNSAT);
  } else {
    init_smt2_context(g);
    code = yices_assert_formulas(g->ctx, g->assertions.size, g->assertions.data);
    if (code < 0) {
      // error during assertion processing
      print_yices_error(true);
      done = true;
      return;
    }
    init_search_parameters(g);
    if (g->random_seed != 0) {
      g->parameters.random_seed = g->random_seed;
    }
    status = check_sat_with_assumptions(g, &g->parameters, g->unsat_core);
    //    validate_unsat_core(g);
    report_status(g, status);

    if (status == STATUS_ERROR) {
      free_assumptions(g->unsat_core);
      g->unsat_core = NULL;
      done = true;
    }
  }
}

/*
 * Check sat with assumptions
 */
static void check_delayed_assertions_assuming(smt2_globals_t *g, uint32_t n, signed_symbol_t *a) {
  assumptions_and_core_t *assumptions;
  int32_t code;
  smt_status_t status;

  assert(g->unsat_assumptions == NULL);

  assumptions = collect_named_assumptions(n, a);
  if (assumptions != NULL) {
    g->frozen = true;
    g->unsat_assumptions = assumptions;
    if (g->trivially_unsat) {
      // list of unsat assumption is empty
      assumptions->status = STATUS_UNSAT;
      report_status(g, STATUS_UNSAT);
    } else {
      init_smt2_context(g);
      code = yices_assert_formulas(g->ctx, g->assertions.size, g->assertions.data);
      if (code < 0) {
        // error during assertion processing
        print_yices_error(true);
        done = true;
        return;
      }
      init_search_parameters(g);
      if (g->random_seed != 0) {
        g->parameters.random_seed = g->random_seed;
      }
      status = check_sat_with_assumptions(g, &g->parameters, assumptions);
      report_status(g, status);

      if (status == STATUS_ERROR) {
        // cleanup
        free_assumptions(assumptions);
        g->unsat_assumptions = NULL;
        done = true;
      }
    }
  }
}

/*
 * Check sat with model assumptions
 */
static void check_delayed_assertions_assuming_model(smt2_globals_t *g, uint32_t n, const term_t vars[], const term_t values[]) {
  int32_t code;
  smt_status_t status;

  g->frozen = true;
  if (g->trivially_unsat) {
    // list of unsat assumption is empty
    report_status(g, STATUS_UNSAT);
    g->check_with_model_status = STATUS_UNSAT;
  } else {
    init_smt2_context(g);
    code = yices_assert_formulas(g->ctx, g->assertions.size, g->assertions.data);
    if (code < 0) {
      // error during assertion processing
      print_yices_error(true);
      done = true;
      return;
    }
    init_search_parameters(g);
    if (g->random_seed != 0) {
      g->parameters.random_seed = g->random_seed;
    }
    status = check_sat_with_model(g, &g->parameters, n, vars, values);
    report_status(g, status);
  }
}


/*
 * EXISTS/FORALL SOLVER
 */

/*
 * Call the exists/forall solver on the delayed assertions
 * - print the status or an error message.
 */
static void efsolve_cmd(smt2_globals_t *g) {
  ef_client_t *efc;

  if (g->efmode) {
    efc = &g->ef_client;
    if (g->timeout != 0) {
      if (! g->to) {
        g->to = init_timeout();
      }
      g->interrupted = false;
      start_timeout(g->to, g->timeout, timeout_handler, g);
    }

    ef_solve(efc, g->assertions.size, g->assertions.data, &g->parameters,
	     qf_fragment(g->logic_code), ef_arch_for_logic(g->logic_code),
             g->tracer, &g->term_patterns);
    if (g-> timeout != 0) clear_timeout(g->to);

    if (efc->efcode != EF_NO_ERROR) {
      // error in preprocessing
      print_ef_analyze_error(efc->efcode);
    } else {
      report_ef_status(g, efc);
    }
  } else {
    print_error("(ef-solve) not supported.");
  }
}






/*
 * CONTEXT OPERATIONS: INCREMENTAL MODE
 */

/*
 * Cleanup before operations that change the context:
 * - delete the model and the core if any
 * - if the context is SAT or UNKNOWN, clear the current assignment
 * - if the context is UNSAT, remove assumptions if any
 *
 * After this: the status can be either IDLE or UNSAT.
 * UNSAT means that there were no assumptions.
 */
static void cleanup_context(smt2_globals_t *g) {
  if (g->model != NULL) {
    yices_free_model(g->model);
    g->model = NULL;
  }
  if (g->unsat_core != NULL) {
    free_assumptions(g->unsat_core);
    g->unsat_core = NULL;
  }
  if (g->unsat_assumptions != NULL) {
    free_assumptions(g->unsat_assumptions);
    g->unsat_assumptions  = NULL;
  }
  g->check_with_model_status = STATUS_IDLE;

  switch (context_status(g->ctx)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    // return to IDLE
    context_clear(g->ctx);
    assert(context_status(g->ctx) == STATUS_IDLE);
    break;

  case STATUS_UNSAT:
    // try to to remove assumptions
    context_clear_unsat(g->ctx);
    assert (context_status(g->ctx) == STATUS_IDLE ||
            context_status(g->ctx) == STATUS_UNSAT);
    break;

  case STATUS_IDLE:
    break;

  case STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
  default:
    bad_status_bug(g->err);
    break;
  }
}

#if 0
static void show_assertion(smt2_globals_t *g, term_t t) {
  smt2_pp_t printer;

  fprintf(g->out, "--- All terms ---\n");
  pp_term_table(g->out, __yices_globals.terms);
  fprintf(g->out, "\n");

  fprintf(g->out, "\nadd_assertion\n");
  init_pretty_printer(&printer, g);
  pp_term_full(&printer.pp, __yices_globals.terms, t);
  flush_smt2_pp(&printer);
  delete_smt2_pp(&printer, true);
}
#endif

/*
 * Assert t in g->ctx
 * - t is known to be a Boolean term here
 * - the context is either IDLE or UNSAT
 */
static void add_assertion(smt2_globals_t *g, term_t t) {
  int32_t code;

  assert(g->ctx != NULL && context_supports_pushpop(g->ctx));

  //  show_assertion(g, t);

  switch (context_status(g->ctx)) {
  case STATUS_IDLE:
    code = assert_formula(g->ctx, t);
    if (code < 0) {
      print_internalization_error(code);
    } else {
      report_success();
    }
    break;

  case STATUS_UNSAT:
    /*
     * Ignore the assertion. We don't try to check whether
     * t is a correct assertion (e.g., no free variables in t).
     */
    report_success();
    break;

  case STATUS_UNKNOWN:
  case STATUS_SAT:
  case STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
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

  if (g->unsat_assumptions != NULL || g->check_with_model_status != STATUS_IDLE) {
    /*
     * the context's status was based on the assumptions or assumed model
     * we reset everything here to be safe.
     */
    cleanup_context(g);
  }

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
      g->parameters.random_seed = g->random_seed;
    }
    stat = check_sat_with_timeout(g, &g->parameters);
    report_status(g, stat);
    break;

  case STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
  default:
    bad_status_bug(g->err);
    break;
  }
}


/*
 * Check sat and compute an unsat core
 */
static void ctx_unsat_core(smt2_globals_t *g) {
  smt_status_t stat;

  assert(g->ctx != NULL && g->produce_unsat_cores &&
         context_supports_pushpop(g->ctx));

  if (g->unsat_core != NULL) {
    // nothing has changed since the previous call to check_sat
    show_status(g->unsat_core->status);
  } else {
    // we build this first, even if the context is SAT or UNSAT
    g->unsat_core = collect_named_assertions(g);
    stat = context_status(g->ctx);
    switch (stat) {
    case STATUS_UNSAT:
      // already solved: store the status and print it
      // the unsat core is empty
      g->unsat_core->status = stat;
      show_status(stat);
      break;

    case STATUS_IDLE:
      // change the seed if needed
      if (g->random_seed != 0) {
        g->parameters.random_seed = g->random_seed;
      }
      stat = check_sat_with_assumptions(g, &g->parameters, g->unsat_core);
      report_status(g, stat);
      if (stat == STATUS_ERROR) {
        free_assumptions(g->unsat_core);
        g->unsat_core = NULL;
      }
      break;

    case STATUS_SAT:
    case STATUS_UNKNOWN:
      // this should not happen.
    case STATUS_SEARCHING:
    case YICES_STATUS_INTERRUPTED:
    default:
      bad_status_bug(g->err);
      break;
    }
  }
}


/*
 * Check with assumptions
 */
static void ctx_check_sat_assuming(smt2_globals_t *g, uint32_t n, signed_symbol_t *a) {
  assumptions_and_core_t *assumptions;
  smt_status_t status;

  cleanup_context(g);

  assert(g->unsat_assumptions == NULL);

  assumptions = collect_named_assumptions(n, a);

  if (assumptions != NULL) {
    g->unsat_assumptions = assumptions;
    switch (context_status(g->ctx)) {
    case STATUS_IDLE:
      if (g->random_seed != 0) {
        g->parameters.random_seed = g->random_seed;
      }
      status = check_sat_with_assumptions(g, &g->parameters, assumptions);
      report_status(g, status);
      if (status == STATUS_ERROR) {
        free_assumptions(assumptions);
        g->unsat_assumptions = NULL;
        done = true;
      }
      break;

    case STATUS_UNSAT:
      // the context is already unsat so the list of unsat assumptions is empty
      assumptions->status = STATUS_UNSAT;
      show_status(STATUS_UNSAT);
      break;

    case STATUS_UNKNOWN:
    case STATUS_SAT:
    case STATUS_SEARCHING:
    case YICES_STATUS_INTERRUPTED:
    default:
      bad_status_bug(g->err);
      break;
    }
  }
}

/*
 * Check with assumptions
 */
static void ctx_check_sat_assuming_model(smt2_globals_t *g, uint32_t n, const term_t vars[], const term_t values[]) {
  smt_status_t status;

  cleanup_context(g);

  switch (context_status(g->ctx)) {
  case STATUS_IDLE:
    if (g->random_seed != 0) {
      g->parameters.random_seed = g->random_seed;
    }
    status = check_sat_with_model(g, &g->parameters, n, vars, values);
    report_status(g, status);
    break;

  case STATUS_UNSAT:
    show_status(STATUS_UNSAT);
    break;

  case STATUS_UNKNOWN:
  case STATUS_SAT:
  case STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
  default:
    bad_status_bug(g->err);
    break;
  }
}


/*
 * New assertion scope
 */
static void ctx_push(smt2_globals_t *g) {
  assert(g->ctx != NULL && context_supports_pushpop(g->ctx));

  cleanup_context(g);

  switch (context_status(g->ctx)) {
  case STATUS_IDLE:
    context_push(g->ctx);
    break;

  case STATUS_UNSAT:
    g->pushes_after_unsat ++;
    break;

  case STATUS_UNKNOWN:
  case STATUS_SAT:
  case STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
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

  cleanup_context(g);

  switch (context_status(g->ctx)) {
  case STATUS_IDLE:
    context_pop(g->ctx);
    break;

  case STATUS_UNSAT:
    if (g->pushes_after_unsat > 0) {
      g->pushes_after_unsat --;
    } else {
      context_clear_unsat(g->ctx);
      context_pop(g->ctx);
    }
    break;

  case STATUS_UNKNOWN:
  case STATUS_SAT:
  case STATUS_SEARCHING:
  case YICES_STATUS_INTERRUPTED:
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
        // g->model should be not NULL
        assert(g->trivially_sat);
        freport_bug(__smt2_globals.err, "get-model");
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

      case YICES_STATUS_INTERRUPTED:
	print_error("the search was interrupted. No model is available");
	break;

      case STATUS_SEARCHING:
      default:
        print_out("BUG: unexpected context status");
        freport_bug(__smt2_globals.err, "BUG: unexpected context status");
        break;
      }
    }
    g->model = mdl;
  }

  return mdl;
}


/*
 * Try to construct a model from the exists/forall solver
 * - return NULL and print an error if the solver's status is not SAT
 */
static model_t *get_ef_model(smt2_globals_t *g) {
  ef_solver_t *efsolver;
  model_t *mdl;
  efmodel_error_code_t code;

  efsolver = g->ef_client.efsolver;
  mdl = ef_get_model(&g->ef_client, &code);

  switch (code) {
  case EFMODEL_CODE_NO_ERROR:
    break;

  case EFMODEL_CODE_NO_MODEL:
    if (efsolver->status == EF_STATUS_UNSAT) {
      print_error("the context is unsatisfiable");
    } else {
      print_error("the exists/forall solver did not find a model");
    }
    break;

  case EFMODEL_CODE_NOT_SOLVED:
    print_error("can't build a model. Call (check-sat) first");
    break;
  }

  return mdl;
}


/*
 * Print value (<SMT2-expression> <value>)
 * - printer = pretty printer object
 * - vtbl = value table where v is stored
 * - token_queue = whatever was parsed
 * - tau = type of the term to print
 * - i = index of the SMT2 expression for t in token_queue
 */
static void print_term_value(smt2_pp_t *printer, value_table_t *vtbl, etk_queue_t *token_queue, value_t v, type_t tau, int32_t i) {
  pp_open_block(&printer->pp, PP_OPEN_PAR);
  pp_smt2_expr(&printer->pp, token_queue, i);
  if (__smt2_globals.clean_model_format) {
    smt2_pp_object(printer, vtbl, v);
  } else {
    smt2_pp_smt2_object(printer, vtbl, v, tau);
  }
  pp_close_block(&printer->pp, true);
}


/*
 * Print a list of pairs terms/values
 * - the list of terms an array of n expression indices expr[0..n-1]
 *   where expr[i] is an valid start index in token_queue
 * - the corresponding values are in v[0 ... n-1]
 * - the corresponding types are in tau[0 ... n-1]
 */
static void print_term_value_list(smt2_pp_t *printer, value_table_t *vtbl, etk_queue_t *token_queue,
                                  int32_t *expr, value_t *v, type_t *tau, uint32_t n) {
  uint32_t i;
  value_t x, u;

  u = vtbl_mk_unknown(vtbl);

  pp_open_block(&printer->pp, PP_OPEN_VPAR); // open '('
  for (i=0; i<n; i++) {
    x = v[i];
    if (x < 0) x = u;
    print_term_value(printer, vtbl, token_queue, x, tau[i], expr[i]);
  }
  pp_close_block(&printer->pp, true); // close ')'
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
 * Collect the types of every term in array t[]
 * - n = number of terms in this arrray
 * - add the types in order to vector v
 */
static void collect_term_types(term_t *t, uint32_t n, ivector_t *v) {
  term_table_t *terms;
  uint32_t i;
  type_t tau;

  terms = __yices_globals.terms;

  ivector_reset(v);
  resize_ivector(v, n);
  for (i=0; i<n; i++) {
    tau = term_type(terms, t[i]);
    ivector_push(v, tau);
  }
}



/*
 * SUPPORT FOR SMT2-STYLE MODEL DISPLAY
 */

/*
 * Helper data structure:
 * - the yices model
 * - three vectors for name, term, term value
 */
typedef struct smt2_model_s {
  model_t *model;
  pvector_t names;
  ivector_t terms;
  ivector_t values;
} smt2_model_t;

/*
 * Initialization/deletion
 */
static void init_smt2_model(smt2_model_t *sm, model_t *m) {
  sm->model = m;
  init_pvector(&sm->names, 0);
  init_ivector(&sm->terms, 0);
  init_ivector(&sm->values, 0);
}

static void delete_smt2_model(smt2_model_t *sm) {
  sm->model = NULL;
  delete_pvector(&sm->names);
  delete_ivector(&sm->terms);
  delete_ivector(&sm->values);
}

/*
 * Add pair (name, t) to sm:
 */
static void smt2_model_push(smt2_model_t *sm, char *name, term_t t) {
  assert(name != NULL && t != NULL_TERM);
  pvector_push(&sm->names, name);
  ivector_push(&sm->terms, t);
}

/*
 * Evaluate all the terms. Store their values in sm->values.
 */
static void smt2_model_eval_terms(smt2_model_t *sm) {
  evaluate_term_values(sm->model, sm->terms.data, sm->terms.size, &sm->values);
}

/*
 * Print the values of all terms in the model
 * - use the SMT-LIB2 format
 */
static void print_smt2_model(smt2_pp_t *printer, smt2_model_t *sm) {
  value_table_t *vtbl;
  term_table_t *terms;
  uint32_t i, n;
  term_t t;
  type_t tau;
  value_t v;

  assert(sm->names.size == sm->terms.size && sm->names.size == sm->values.size);

  terms = __yices_globals.terms;
  vtbl = model_get_vtbl(sm->model);

  pp_open_block(&printer->pp, PP_OPEN_TPAR);

  n = sm->names.size;
  for (i=0; i<n; i++) {
    t = sm->terms.data[i];
    v = sm->values.data[i];
    assert(good_term(terms, t));

    /*
     * t = a term
     * v = value in the model as returned by eval_in_model(t)
     * if v < 0, then eval_in_model failed, so we skip t.
     */
    if (good_object(vtbl, v)) {
      tau = term_type(terms, t);
      smt2_pp_def(printer, vtbl, sm->names.data[i], tau, v);
    }
  }
  pp_close_block(&printer->pp, true);

}


/*
 * Check whether t is uninterpreted
 */
static bool term_is_uninterpreted(term_t t) {
  return t != NULL_TERM && is_pos_term(t) && term_kind(__yices_globals.terms, t) == UNINTERPRETED_TERM;
}


/*
 * Build an smt2_model:
 * - collect the names of all declared uninterpreted terms
 *   and add them to the smt2_model
 * - first, scan vector g->model_term_names
 *   then scan the stack g->term_names.
 */
static void build_smt2_model(smt2_globals_t *g, smt2_model_t *sm) {
  pvector_t *saved;
  smt2_name_stack_t *name_stack;
  char *name;
  term_t t;
  uint32_t i, n;

  assert(sm->names.size == 0 && sm->terms.size == 0 && sm->values.size == 0);

  saved = &g->model_term_names;
  n = saved->size;
  for (i=0; i<n; i++) {
    name = saved->data[i];
    t = yices_get_term_by_name(name);
    assert(term_is_uninterpreted(t));
    smt2_model_push(sm, name, t);
  }

  name_stack = &g->term_names;
  n = name_stack->top;
  for (i=0; i<n; i++) {
    name = name_stack->names[i];
    t = yices_get_term_by_name(name);
    if (term_is_uninterpreted(t)) {
      smt2_model_push(sm, name, t);
    }
  }

  smt2_model_eval_terms(sm);

  assert(sm->names.size == sm->terms.size && sm->names.size == sm->values.size);
}





/*
 * GET ASSIGNMENT
 */

/*
 * Print pair (name val) where val is a Boolean value
 */
static void print_bool_assignment(smt2_pp_t *printer, const char *name, bval_t val) {
  pp_open_block(&printer->pp, PP_OPEN_PAR); // '('
  smt2_pp_symbol(printer, name);
  if (bval_is_undef(val)) {
    pp_string(&printer->pp, "???");
  } else {
    pp_bool(&printer->pp, bval2bool(val));
  }
  pp_close_block(&printer->pp, true); // close ')'
}


/*
 * Convert an object v in vtbl to a bval
 */
static bval_t obj2bval(value_table_t *vtbl, value_t v) {
  bval_t b;

  b = VAL_UNDEF_FALSE;
  if (is_true(vtbl, v)) {
    b = VAL_TRUE;
  } else if (is_false(vtbl, v)) {
    b = VAL_FALSE;
  }
  return b;
}

/*
 * Model assignment: this is called when Yices is used in benchmark
 * mode, and all assertions simplify to true. In this case, the
 * assertions are trivially satisfiable, no context is
 * constructed, but we have a model.
 *
 * This is also used to print assignments when we use the ef-solver.
 *
 * We print whatever default values get assigned to the
 * boolean terms in the model.
 */
static void print_model_assignment(smt2_pp_t *printer, named_term_stack_t *s, model_t *mdl) {
  evaluator_t evaluator;
  value_table_t *vtbl;
  uint32_t i, n;
  value_t v;

  vtbl = model_get_vtbl(mdl);
  init_evaluator(&evaluator, mdl);
  pp_open_block(&printer->pp, PP_OPEN_VPAR);  // open '('
  n = s->top;
  for (i=0; i<n; i++) {
    v = eval_in_model(&evaluator, s->data[i].term);
    print_bool_assignment(printer, s->data[i].name, obj2bval(vtbl, v));
  }
  pp_close_block(&printer->pp, true);  // close ')'
  delete_evaluator(&evaluator);
}


/*
 * Non-trivial assignment: go through the list of all named Booleans
 * - query the context to get each term value
 * - if a value is unknown, print the default 'true'
 */
static void print_assignment(smt2_pp_t *printer, context_t *ctx, named_term_stack_t *s) {
  uint32_t i, n;
  bval_t v;

  pp_open_block(&printer->pp, PP_OPEN_VPAR);
  n = s->top;
  for (i=0; i<n; i++) {
    v = context_bool_term_value(ctx, s->data[i].term);
    print_bool_assignment(printer, s->data[i].name, v);
  }
  pp_close_block(&printer->pp, true);
}



/*
 * Show assignment of all named booleans
 * - check whether we have a context first
 */
static void show_assignment(smt2_globals_t *g) {
  smt2_pp_t printer;

  if (g->ctx == NULL) {
    assert(g->benchmark_mode);

    if (!g->frozen) {
      print_error("can't build the assignment. Call (check-sat) first");
    } else if (g->trivially_unsat) {
      print_error("the context is unsatisfiable");
    } else {
      assert(g->trivially_sat && g->model != NULL);
      init_pretty_printer(&printer, g);
      print_model_assignment(&printer, &g->named_bools, g->model);
      delete_smt2_pp(&printer, true);
    }

  } else {
    switch (context_status(g->ctx)) {
    case STATUS_UNKNOWN:
    case STATUS_SAT:
      init_pretty_printer(&printer, g);
      print_assignment(&printer, g->ctx, &g->named_bools);
      delete_smt2_pp(&printer, true);
      break;

    case STATUS_UNSAT:
      print_error("the context is unsatisfiable");
      break;

    case STATUS_IDLE:
      print_error("can't build the assignment. Call (check-sat) first");
      break;

    case YICES_STATUS_INTERRUPTED:
      print_error("can't build the assignment. The search was interrupted");
      break;

    case STATUS_SEARCHING:
    default:
      print_out("BUG: unexpected context status");
      freport_bug(__smt2_globals.err, "BUG: unexpected context status");
      break;
    }
  }
}


/*
 * Show assignment in exists/forall mode
 */
static void show_ef_assignment(smt2_globals_t *g) {
  model_t *mdl;
  smt2_pp_t printer;

  mdl = get_ef_model(g);
  if (mdl == NULL) return;

  init_pretty_printer(&printer, g);
  print_model_assignment(&printer, &g->named_bools, mdl);
  delete_smt2_pp(&printer, true);
}


/*
 * UNSAT CORE AND UNSAT ASSUMPTIONS
 */

/*
 * For every term in a core, print its id.
 * The id is stored in the assumption table and is either a name or (not name)
 */
static void print_assumption_list(smt2_pp_t *printer, assumption_table_t *table, uint32_t n, term_t *a) {
  assumption_t *d;
  uint32_t i;

  pp_open_block(&printer->pp, PP_OPEN_PAR);
  for (i=0; i<n; i++) {
    d = assumption_table_get(table, a[i]);
    assert(d != NULL);
    if (! d->polarity) pp_open_block(&printer->pp, PP_OPEN_NOT);
    smt2_pp_symbol(printer, d->name);
    if (! d->polarity) pp_close_block(&printer->pp, true);
  }
  pp_close_block(&printer->pp, true);
}

/*
 * Print the unsat core if any
 */
static void show_unsat_core(smt2_globals_t *g) {
  smt2_pp_t printer;
  assumptions_and_core_t *unsat_core;

  if (! g->produce_unsat_cores) {
    print_error("not supported: :produce-unsat-cores is false");
  } else {
    unsat_core = g->unsat_core;
    if (unsat_core == NULL) {
      print_error("Can't build an unsat core. Call (check-sat) first");
    } else {
      switch (unsat_core->status) {
      case STATUS_UNKNOWN:
      case STATUS_SAT:
        print_error("No unsat core. The context is satisfiable");
        break;

      case STATUS_UNSAT:
        init_pretty_printer(&printer, g);
        print_assumption_list(&printer, &unsat_core->table,
                              unsat_core->core.size, unsat_core->core.data);
        delete_smt2_pp(&printer, true);
        break;

      case YICES_STATUS_INTERRUPTED:
	print_error("No unsat core. The search was interrupted");
	break;

      case STATUS_IDLE:
      case STATUS_SEARCHING:
      default:
        print_out("BUG: unexpected status in get-unsat-core");
        freport_bug(__smt2_globals.err, "BUG: unexpected status in get-unsat-core");
        break;
      }
    }
  }
}

/*
 * Print the list of unsat assumptions if any
 */
static void show_unsat_assumptions(smt2_globals_t *g) {
  smt2_pp_t printer;
  assumptions_and_core_t *unsat_assumptions;

  if (!g->produce_unsat_assumptions) {
    print_error("not supported: :produce-unsat-assumptions is false");
  } else {
    unsat_assumptions = g->unsat_assumptions;
    if (unsat_assumptions == NULL) {
      print_error("Call (check-sat-assuming) first");
    } else {
      switch (unsat_assumptions->status) {
      case STATUS_UNKNOWN:
      case STATUS_SAT:
        print_error("No unsat assumptions. The context is satisfiable");
        break;

      case STATUS_UNSAT:
        init_pretty_printer(&printer, g);
        print_assumption_list(&printer, &unsat_assumptions->table,
                              unsat_assumptions->core.size, unsat_assumptions->core.data);
        delete_smt2_pp(&printer, true);
        break;

      case YICES_STATUS_INTERRUPTED:
	print_error("No unsat assumptions. The search was interrupted");
	break;

      case STATUS_IDLE:
      case STATUS_SEARCHING:
      default:
        print_out("BUG: unexpected status in get-unsat-assumptions");
        freport_bug(__smt2_globals.err, "BUG: unexpected status in get-unsat-assumptions");
        break;
      }
    }
  }
}

/*
 * Print the the model interpolant if any
 */
static void show_unsat_model_interpolant(smt2_globals_t *g) {
  smt2_pp_t printer;
  term_t unsat_model_interpolant;

  if (!g->produce_unsat_model_interpolants) {
    print_error("not supported: :produce-unsat-model-interpolants is false");
  } else if (g->ctx == NULL) {
    if (g->check_with_model_status == STATUS_UNSAT) {
      print_out("false");
      flush_out();
    } else {
      print_error("Call (check-sat-assuming-model) first");
    }
  } else {
    switch (context_status(g->ctx)) {
    case STATUS_SAT:
      print_error("No model interpolant. The context is satisfiable");
      break;

    case STATUS_UNKNOWN:
      print_error("No model interpolant. The context is not knwon to be unsatisfiable");
      break;

    case STATUS_UNSAT:
      unsat_model_interpolant = context_get_unsat_model_interpolant(g->ctx);
      if (unsat_model_interpolant == NULL_TERM) {
        print_error("Call (check-sat-assuming-model) first");
      } else {
        init_pretty_printer(&printer, g);
        pp_term_full(&printer.pp, __yices_globals.terms, unsat_model_interpolant);
        delete_smt2_pp(&printer, true);
      }
      break;

    case STATUS_IDLE:
      print_error("Call (check-sat-assuming-model) first");
      break;

    case YICES_STATUS_INTERRUPTED:
      print_error("No model interpolant. Last call to check-sat timedout");
      break;

    case STATUS_SEARCHING:
    default:
      print_out("BUG: unexpected status in get-unsat-model-interpolant");
      freport_bug(__smt2_globals.err, "BUG: unexpected status in get-unsat-model-interpolant");
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

// test whether we must save names
static inline bool saving_names(const smt2_globals_t *g) {
  return !g->global_decls && smt2_stack_is_nonempty(&g->stack);
}

static void save_name(smt2_globals_t *g, smt2_name_stack_t *name_stack, const char *s) {
  char *clone;

  if (saving_names(g)) {
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
 * For debugging: check that the stack looks reasonable
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
      freport_bug(g->err, "Invalid stack: levels don't match");
    }

    if (context_base_level(g->ctx) + g->pushes_after_unsat != stack->top) {
      freport_bug(g->err, "Internal error: unexpected context status");
    }

    if (g->pushes_after_unsat > 0 && context_status(g->ctx) != STATUS_UNSAT) {
      freport_bug(g->err, "Invalid stack: push_after_unsat is positive but context is not unsat");
    }
  }
}

#else

// Do nothing
static inline void check_stack(smt2_globals_t *g) {
}

#endif


/*
 * SYMBOL NAMES FOR MODEL DISPLAY
 */

/*
 * The names stored in g->model_term_names are strings with reference
 * count. We push a name in this vector when we process
 *
 *  (declare-fun <name> ....)
 *
 * if g->clean_model_format is false and if we know that the name
 * is not already saved in the term_stack.
 */

/*
 * Free all strings in vector v then reset the vector
 */
static void reset_string_vector(pvector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    string_decref(v->data[i]);
  }
  pvector_reset(v);
}

/*
 * Free all strings in vector v then delete the vector
 */
static void delete_string_vector(pvector_t *v) {
  reset_string_vector(v);
  delete_pvector(v);
}

/*
 * Add string s at the end v
 * - s must be a refcount string
 * - its reference counter is incremented
 */
static void string_vector_push(pvector_t *v, char *s) {
  string_incref(s);
  pvector_push(v, s);
}


/*
 * Save name if it may be needed later to display a model
 * - we don't do anything if g->clean_model_format is true
 *   or if the name has already been saved in g->term_names.
 */
static void save_name_for_model(smt2_globals_t *g, const char *s) {
  char *clone;

  if (!g->clean_model_format && !saving_names(g)) {
    clone = clone_string(s);
    string_vector_push(&g->model_term_names, clone);
  }
}




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
        assert(g->trivially_sat);
        print_error("the context is satisfiable");
      }
    } else {
      switch (context_status(g->ctx)) {
      case STATUS_UNKNOWN:
        if (g->interrupted) {
          print_kw_symbol_pair(":reason-unknown", "timeout");
        } else {
          print_kw_symbol_pair(":reason-unknown", "incomplete");
        }
        flush_out();
        break;

      case STATUS_SAT:
        print_error("the context is satisfiable");
        break;

      case STATUS_UNSAT:
        print_error("the context is unsatisfiable");
        break;

      case STATUS_IDLE:
        if (g->timeout > 0 && g->interrupted) {
          print_kw_symbol_pair(":reason-unknown", "timeout");
        } else {
          print_error("can't tell until you call (check-sat)");
        }
        break;

      case STATUS_SEARCHING:
      case YICES_STATUS_INTERRUPTED:
      default:
        print_out("BUG: unexpected context status");
        freport_bug(__smt2_globals.err, "BUG: unexpected context status");
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
  g->clean_model_format = true;
  g->bvconst_in_decimal = false;
  g->smtlib_version = 0;       // means no version specified yet
  g->pushes_after_unsat = 0;
  g->logic_name = NULL;
  g->mcsat = false;
  init_ivector(&g->var_order, 0);
  init_mcsat_options(&g->mcsat_options);
  g->efmode = false;
  init_ef_client(&g->ef_client);
  g->export_to_dimacs = false;
  g->dimacs_file = NULL;
  g->out = stdout;
  g->err = stderr;
  g->out_name = NULL;
  g->err_name = NULL;
  g->out_fd = fileno(stdout);
  g->err_fd = fileno(stderr);
  g->tracer = NULL;
  g->print_success = false;  // the standard says that this should be true??
  g->expand_definitions = false;
  g->interactive_mode = false;
  g->produce_proofs = false;
  g->produce_unsat_cores = false;
  g->produce_unsat_assumptions = false;
  g->produce_unsat_model_interpolants = false;
  g->produce_models = false;
  g->produce_assignments = false;
  g->random_seed = 0;  // 0 means any seed is good
  g->verbosity = 0;
  init_ctx_params(&g->ctx_parameters);
  init_params_to_defaults(&g->parameters);
  g->dump_models = false;
  g->nthreads = 0;
  g->timeout = 0;
  g->to = NULL;
  g->interrupted = false;
  g->delegate = NULL;
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

  init_pvector(&g->model_term_names, 0);

  g->unsat_core = NULL;
  g->unsat_assumptions = NULL;
  g->check_with_model_status = STATUS_IDLE;

  init_etk_queue(&g->token_queue);
  init_ivector(&g->token_slices, 0);
  init_ivector(&g->val_vector, 0);
  init_ivector(&g->type_vector, 0);

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
  g->trivially_sat = false;
  g->frozen = false;

  init_smt2_pattern_map(&g->term_patterns);
}


/*
 * Cleanup: close out and err if different from the defaults
 * - delete all internal structures (except avtbl)
 * - delete the timeout object if it's initialized
 */
static void delete_smt2_globals(smt2_globals_t *g) {
  if (g->to) {
    delete_timeout(g->to);
  }
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
  if (g->efmode) {
    delete_ef_client(&g->ef_client);
  }
  delete_ivector(&g->assertions);
  delete_ivector(&g->var_order);

  delete_smt2_pattern_map(&g->term_patterns);

  delete_smt2_stack(&g->stack);
  delete_smt2_name_stack(&g->term_names);
  delete_smt2_name_stack(&g->type_names);
  delete_smt2_name_stack(&g->macro_names);

  delete_named_term_stack(&g->named_bools);
  delete_named_term_stack(&g->named_asserts);

  delete_string_vector(&g->model_term_names);

  if (g->unsat_core != NULL) {
    free_assumptions(g->unsat_core);
    g->unsat_core = NULL;
  }
  if (g->unsat_assumptions != NULL) {
    free_assumptions(g->unsat_assumptions);
    g->unsat_assumptions = NULL;
  }

  delete_etk_queue(&g->token_queue);
  delete_ivector(&g->token_slices);
  delete_ivector(&g->val_vector);
  delete_ivector(&g->type_vector);

  close_output_file(g);
  close_error_file(g);
  delete_tracer(g);
}


/*
 * Initialize all internal structures
 * - benchmark: if true, the input is assumed to be an SMT-LIB benchmark
 *   (i.e., a set of assertions followed by a single call to check-sat)
 *   In this mode,
 *   - destructive simplifications are allowed.
 *   - push/pop are not supported
 *   - assert can't be used after (check-sat)
 *
 * - timeout = timeout to use (in seconds).
 *   If this is zero, no timeout is used.
 *
 * - print_success = initial setting of the :print-success option.
 *
 * This function is called after yices_init so all Yices internals are ready
 */
void init_smt2(bool benchmark, uint32_t timeout, bool print_success) {
  done = false;
  init_smt2_globals(&__smt2_globals);
  init_attr_vtbl(&avtbl);
  __smt2_globals.avtbl = &avtbl;
  if (benchmark) {
    __smt2_globals.benchmark_mode = true;
    __smt2_globals.global_decls = true;
  }
  __smt2_globals.timeout = timeout;
  __smt2_globals.print_success = print_success;
  check_stack(&__smt2_globals);
}

void init_mt2(bool benchmark, uint32_t timeout, uint32_t nthreads, bool print_success){
  init_smt2(benchmark, timeout, print_success);
  __smt2_globals.nthreads = nthreads;
  //fprintf(stderr, "nthreads = %"PRIu32"\n", nthreads);
}



/*
 * Force verbosity level to k
 */
void smt2_set_verbosity(uint32_t k) {
  __smt2_globals.verbosity = k;
  update_trace_verbosity(&__smt2_globals);
}

/*
 * Enable a trace tag for tracing
 */
void smt2_enable_trace_tag(const char* tag) {
  tracer_t* tracer;

  tracer = get_tracer(&__smt2_globals);
  enable_trace_tag(tracer, tag);
}

/*
 * Force models to be printed in SMT2 format (as much as possible).
 */
void smt2_force_smt2_model_format(void) {
  __smt2_globals.clean_model_format = false;
}

/*
 * Select to print bit-vector constant in the SMT2 'decimal' format
 */
void smt2_force_bvdecimal_format(void) {
  __smt2_globals.bvconst_in_decimal = true;
}

/*
 * Bitblast and export to DIMACS
 */
void smt2_export_to_dimacs(const char *filename) {
  __smt2_globals.export_to_dimacs = true;
  __smt2_globals.dimacs_file = filename;
}

/*
 * Display all statistics
 */
void smt2_show_stats(void) {
  show_statistics(&__smt2_globals);
}


/*
 * Set a delegate:
 * - name = name of an external sat solver to use for QF_BV problems
 */
void smt2_set_delegate(const char *name) {
  assert(name != NULL);
  __smt2_globals.delegate = name;
}

/*
 * Set a a dimacs filename but don't force export to DIMACS
 * This is use to export to DIMACS after delegate preprocessing
 */
void smt2_set_dimacs_file(const char *filename) {
  __smt2_globals.export_to_dimacs = false;
  __smt2_globals.dimacs_file = filename;
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
    trace_printf(__smt2_globals.tracer, 12, "\n(%s: 1 call)\n", cmd);
  } else {
    trace_printf(__smt2_globals.tracer, 12, "\n(%s: %"PRIu32" calls)\n", cmd, calls);
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
    if (__smt2_globals.efmode) {
      show_ef_assignment(&__smt2_globals);
    } else {
      show_assignment(&__smt2_globals);
    }
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


#if 0
/*
 * Provisional: print the named assertions
 */
static void print_named_assertions(named_term_stack_t *s) {
  uint32_t i, n;
  const char *name;

  n = s->top;
  printf("=== %"PRIu32" named assertions ===\n", n);
  for (i=0; i<n; i++) {
    name = s->data[i].name;
    if (symbol_needs_quotes(name)) {
      printf("   assertion[%"PRIu32"]: name = |%s|, term = %"PRId32"\n", i, name, s->data[i].term);
    } else {
      printf("   assertion[%"PRIu32"]: name = %s, term = %"PRId32"\n", i, name, s->data[i].term);
    }
  }
  printf("\n");
}

#endif


/*
 * Get the unsat core: subset of :named assertions that form an unsat core
 */
void smt2_get_unsat_core(void) {
  __smt2_globals.stats.num_get_unsat_core ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("get-unsat-core", __smt2_globals.stats.num_get_unsat_core);

  if (check_logic()) {
    if (__smt2_globals.efmode) {
      print_error("get-unsat-core is not supported in logic %s", __smt2_globals.logic_name);
    } else {
      show_unsat_core(&__smt2_globals);
    }
  }
}


/*
 * Get the unsat assumptions: subset of :named assertions that form an unsat core
 */
void smt2_get_unsat_assumptions(void) {
  __smt2_globals.stats.num_get_unsat_assumptions ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("get-unsat-assumptions", __smt2_globals.stats.num_get_unsat_assumptions);

  if (check_logic()) {
    if (__smt2_globals.efmode) {
      print_error("get-unsat-assumptions is not supported in logic %s", __smt2_globals.logic_name);
    } else {
      show_unsat_assumptions(&__smt2_globals);
    }
  }
}

/* Check whether MCSAT solver is going to be used. */
static bool mcsat_enabled(smt2_globals_t *g) {
  return g->mcsat || arch_for_logic(g->logic_code) == CTX_ARCH_MCSAT;
}

/*
 * Get the interpolant for the model: formula implied by the assertions that
 * evaluates to false.
 */
void smt2_get_unsat_model_interpolant(void) {
  __smt2_globals.stats.num_get_unsat_model_interpolant ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("get-unsat-model-interpolant", __smt2_globals.stats.num_get_unsat_model_interpolant);

  if (check_logic()) {
    if (!mcsat_enabled(&__smt2_globals)) {
      print_error("get-unsat-model-interpolant is only supported in MCSAT");
    } else {
      show_unsat_model_interpolant(&__smt2_globals);
    }
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
  smt2_pp_t printer;
  etk_queue_t *queue;
  ivector_t *slices;
  ivector_t *values;
  ivector_t *types;
  model_t *mdl;

  __smt2_globals.stats.num_get_value ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("get-value", __smt2_globals.stats.num_get_value);

  if (check_logic()) {
    if (__smt2_globals.efmode) {
      mdl = get_ef_model(&__smt2_globals);
    } else {
      mdl = get_model(&__smt2_globals);
    }
    if (mdl == NULL) return;

    // evaluate all terms: store the values in values->data[0 ... n-1]
    values = &__smt2_globals.val_vector;
    evaluate_term_values(mdl, a, n, values);

    // collect their types in types->data[0 ... n-1]
    types = &__smt2_globals.type_vector;
    collect_term_types(a, n, types);

    queue = &__smt2_globals.token_queue;
    slices = &__smt2_globals.token_slices;
    assert(slices->size == 0);
    assert(good_token(queue, 2) && start_token(queue, 2));
    collect_subexpr(queue, 2, slices);
    assert(slices->size == n);

    init_pretty_printer(&printer, &__smt2_globals);
    print_term_value_list(&printer, &mdl->vtbl, queue, slices->data, values->data, types->data, n);
    delete_smt2_pp(&printer, true);
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
 * Checks if the option should be passed to the yices frontend.
 * In other words returns true in the name begins with ":yices-"
 * if so then it also stores the remainder of the string in *option.
 */
#define YICES_SMT2_PREFIX  ":yices-"

static bool is_yices_option(const char *name, const char **option) {
  uint32_t len;

  len = strlen(YICES_SMT2_PREFIX);
  if (strncmp(name, YICES_SMT2_PREFIX, len) == 0) {
    *option = &name[len];
    return true;
  }
  return false;
}


/*
 * Shows the value of the yices option, and returns true, if supported.
 * If not supported it simply returns false.
 */
static bool yices_get_option(smt2_globals_t *g, yices_param_t p) {
  bool supported;

  supported = true;

  switch (p) {
  case PARAM_VAR_ELIM:
    print_boolean_value(g->ctx_parameters.var_elim);
    break;

  case PARAM_ARITH_ELIM:
    print_boolean_value(g->ctx_parameters.arith_elim);
    break;

  case PARAM_BVARITH_ELIM:
    print_boolean_value(g->ctx_parameters.bvarith_elim);
    break;

  case PARAM_FLATTEN:
    // this activates both flatten or and flatten diseq.
    print_boolean_value(g->ctx_parameters.flatten_or);
    break;

  case PARAM_LEARN_EQ:
    print_boolean_value(g->ctx_parameters.eq_abstraction);
    break;

  case PARAM_KEEP_ITE:
    print_boolean_value(g->ctx_parameters.keep_ite);
    break;

  case PARAM_FAST_RESTARTS:
    print_boolean_value(g->parameters.fast_restart);
    break;

  case PARAM_C_THRESHOLD:
    print_uint32_value(g->parameters.c_threshold);
    break;

  case PARAM_C_FACTOR:
    print_float_value(g->parameters.c_factor);
    break;

  case PARAM_D_THRESHOLD:
    print_uint32_value(g->parameters.d_threshold);
    break;

  case PARAM_D_FACTOR:
    print_float_value(g->parameters.c_factor);
    break;

  case PARAM_R_THRESHOLD:
    print_uint32_value(g->parameters.r_threshold);
    break;

  case PARAM_R_FRACTION:
    print_float_value(g->parameters.r_fraction);
    break;

  case PARAM_R_FACTOR:
    print_float_value(g->parameters.r_factor);
    break;

  case PARAM_VAR_DECAY:
    print_float_value(g->parameters.var_decay);
    break;

  case PARAM_RANDOMNESS:
    print_float_value(g->parameters.randomness);
    break;

  case PARAM_RANDOM_SEED:
    print_uint32_value(g->parameters.random_seed);
    break;

  case PARAM_BRANCHING:
    print_string_value(branching2string[g->parameters.branching]);
    break;

  case PARAM_CLAUSE_DECAY:
    print_float_value(g->parameters.clause_decay);
    break;

  case PARAM_CACHE_TCLAUSES:
    print_boolean_value(g->parameters.cache_tclauses);
    break;

  case PARAM_TCLAUSE_SIZE:
    print_uint32_value(g->parameters.tclause_size);
    break;

  case PARAM_DYN_ACK:
    print_boolean_value(g->parameters.use_dyn_ack);
    break;

  case PARAM_DYN_BOOL_ACK:
    print_boolean_value(g->parameters.use_bool_dyn_ack);
    break;

  case PARAM_OPTIMISTIC_FCHECK:
    print_boolean_value(g->parameters.use_optimistic_fcheck);
    break;

  case PARAM_MAX_ACK:
    print_uint32_value(g->parameters.max_ackermann);
    break;

  case PARAM_MAX_BOOL_ACK:
    print_uint32_value(g->parameters.max_boolackermann);
    break;

  case PARAM_AUX_EQ_QUOTA:
    print_uint32_value(g->parameters.aux_eq_quota);
    break;

  case PARAM_AUX_EQ_RATIO:
    print_float_value(g->parameters.aux_eq_ratio);
    break;

  case PARAM_DYN_ACK_THRESHOLD:
    print_uint32_value((uint32_t) g->parameters.dyn_ack_threshold);
    break;

  case PARAM_DYN_BOOL_ACK_THRESHOLD:
    print_uint32_value((uint32_t) g->parameters.dyn_bool_ack_threshold);
    break;

  case PARAM_MAX_INTERFACE_EQS:
    print_uint32_value(g->parameters.max_interface_eqs);
    break;

  case PARAM_EAGER_LEMMAS:
    print_boolean_value(g->ctx_parameters.splx_eager_lemmas);
    break;

  case PARAM_ICHECK:
    print_boolean_value(g->ctx_parameters.splx_periodic_icheck);
    break;

  case PARAM_SIMPLEX_PROP:
    print_boolean_value(g->parameters.use_simplex_prop);
    break;

  case PARAM_SIMPLEX_ADJUST:
    print_boolean_value(g->parameters.adjust_simplex_model);
    break;

  case PARAM_PROP_THRESHOLD:
    print_uint32_value(g->parameters.max_prop_row_size);
    break;

  case PARAM_BLAND_THRESHOLD:
    print_uint32_value(g->parameters.bland_threshold);
    break;

  case PARAM_ICHECK_PERIOD:
    print_uint32_value(g->parameters.integer_check_period);
    break;

  case PARAM_MAX_UPDATE_CONFLICTS:
    print_uint32_value(g->parameters.max_update_conflicts);
    break;

  case PARAM_MAX_EXTENSIONALITY:
    print_uint32_value(g->parameters.max_extensionality);
    break;

  case PARAM_EF_FLATTEN_IFF:
    print_boolean_value(g->ef_client.ef_parameters.flatten_iff);
    break;

  case PARAM_EF_FLATTEN_ITE:
    print_boolean_value(g->ef_client.ef_parameters.flatten_ite);
    break;

  case PARAM_EF_GEN_MODE:
    print_string_value(efgen2string[g->ef_client.ef_parameters.gen_mode]);
    break;

  case PARAM_EF_MAX_SAMPLES:
    print_uint32_value(g->ef_client.ef_parameters.max_samples);
    break;

  case PARAM_EF_MAX_ITERS:
    print_uint32_value(g->ef_client.ef_parameters.max_iters);
    break;

  case PARAM_EF_MAX_LEMMAS_PER_ROUND:
    print_uint32_value(g->ef_client.ef_parameters.max_numlearnt_per_round);
    break;

  case PARAM_EMATCH_EN:
    print_boolean_value(g->ef_client.ef_parameters.ematching);
    break;

  case PARAM_EMATCH_INST_PER_ROUND:
    print_uint32_value(g->ef_client.ef_parameters.ematch_inst_per_round);
    break;

  case PARAM_EMATCH_INST_PER_SEARCH:
    print_uint32_value(g->ef_client.ef_parameters.ematch_inst_per_search);
    break;

  case PARAM_EMATCH_INST_TOTAL:
    print_uint32_value(g->ef_client.ef_parameters.ematch_inst_total);
    break;

  case PARAM_EMATCH_ROUNDS_PER_SEARCH:
    print_uint32_value(g->ef_client.ef_parameters.ematch_rounds_per_search);
    break;

  case PARAM_EMATCH_SEARCH_TOTAL:
    print_uint32_value(g->ef_client.ef_parameters.ematch_search_total);
    break;

  case PARAM_EMATCH_TRIAL_FDEPTH:
    print_uint32_value(g->ef_client.ef_parameters.ematch_exec_max_fdepth);
    break;

  case PARAM_EMATCH_TRIAL_VDEPTH:
    print_uint32_value(g->ef_client.ef_parameters.ematch_exec_max_vdepth);
    break;

  case PARAM_EMATCH_TRIAL_FAPPS:
    print_uint32_value(g->ef_client.ef_parameters.ematch_exec_max_fapps);
    break;

  case PARAM_EMATCH_TRIAL_MATCHES:
    print_uint32_value(g->ef_client.ef_parameters.ematch_exec_max_matches);
    break;

  case PARAM_EMATCH_CNSTR_MODE:
    print_string_value(ematchmode2string[g->ef_client.ef_parameters.ematch_cnstr_mode]);
    break;

  case PARAM_EMATCH_CNSTR_EPSILON:
    print_uint32_value(g->ef_client.ef_parameters.ematch_cnstr_epsilon);
    break;

  case PARAM_EMATCH_CNSTR_ALPHA:
    print_float_value(g->ef_client.ef_parameters.ematch_cnstr_alpha);
    break;

  case PARAM_EMATCH_TERM_EPSILON:
    print_uint32_value(g->ef_client.ef_parameters.ematch_term_epsilon);
    break;

  case PARAM_EMATCH_TERM_ALPHA:
    print_float_value(g->ef_client.ef_parameters.ematch_term_alpha);
    break;

  case PARAM_EMATCH_TERM_MODE:
    print_string_value(ematchmode2string[g->ef_client.ef_parameters.ematch_term_mode]);
    break;

  case PARAM_MCSAT_NRA_BOUND:
    print_boolean_value(g->mcsat_options.nra_bound);
    break;

  case PARAM_MCSAT_L2O:
    print_boolean_value(g->mcsat_options.l2o);
    break;

  case PARAM_MCSAT_NRA_BOUND_MAX:
    print_int32_value(g->mcsat_options.nra_bound_max);
    break;

  case PARAM_MCSAT_NRA_BOUND_MIN:
    print_int32_value(g->mcsat_options.nra_bound_min);
    break;

  case PARAM_MCSAT_NRA_MGCD:
    print_boolean_value(g->mcsat_options.nra_mgcd);
    break;

  case PARAM_MCSAT_NRA_NLSAT:
    print_boolean_value(g->mcsat_options.nra_nlsat);
    break;

  case PARAM_MCSAT_RAND_DEC_FREQ:
    print_float_value(g->parameters.randomness);
    break;

  case PARAM_MCSAT_RAND_DEC_SEED:
    print_int32_value(g->parameters.random_seed);
    break;

  case PARAM_MCSAT_VAR_ORDER:
    print_terms_value(g, &g->var_order);
    break;

  case PARAM_UNKNOWN:
  default:
    freport_bug(g->err,"invalid parameter id in 'yices_get_option'");
    break;
  }

  return supported;
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
  const char* yices_option;
  yices_param_t p;

  g = &__smt2_globals;
  n = kwlen(name);
  kw = smt2_string_to_keyword(name, n);
  switch (kw) {
  case SMT2_KW_DIAGNOSTIC_OUTPUT:
    s = g->err_name;
    if (s == NULL) {
      assert(g->err == stderr);
      s = "stderr";
    }
    print_string_value(s);
    break;

  case SMT2_KW_GLOBAL_DECLARATIONS:
    print_boolean_value(g->global_decls);
    break;

  case SMT2_KW_PRINT_SUCCESS:
    print_boolean_value(g->print_success);
    break;

  case SMT2_KW_PRODUCE_ASSIGNMENTS:
    print_boolean_value(g->produce_assignments);
    break;

  case SMT2_KW_PRODUCE_MODELS:
    print_boolean_value(g->produce_models);
    break;

  case SMT2_KW_RANDOM_SEED:
    print_uint32_value(g->random_seed);
    break;

  case SMT2_KW_REGULAR_OUTPUT:
    s = g->out_name;
    if (s == NULL) {
      assert(g->out == stdout);
      s = "stdout";
    }
    print_string_value(s);
    break;

  case SMT2_KW_VERBOSITY:
    print_uint32_value(g->verbosity);
    break;

  case SMT2_KW_DUMP_MODELS:
    print_boolean_value(g->dump_models);
    break;

  case SMT2_KW_PRODUCE_UNSAT_ASSUMPTIONS:
    print_boolean_value(g->produce_unsat_assumptions);
    break;

  case SMT2_KW_PRODUCE_UNSAT_CORES:
    print_boolean_value(g->produce_unsat_cores);
    break;

  case SMT2_KW_PRODUCE_UNSAT_MODEL_INTERPOLANTS:
	print_boolean_value(g->produce_unsat_model_interpolants);
	break;

  case SMT2_KW_EXPAND_DEFINITIONS:
  case SMT2_KW_INTERACTIVE_MODE:
  case SMT2_KW_PRODUCE_ASSERTIONS:
  case SMT2_KW_PRODUCE_PROOFS:
  case SMT2_KW_REPRODUCIBLE_RESOURCE_LIMIT:
    unsupported_option();
    flush_out();
    break;

  default:
    // may be a Yices option
    if (is_yices_option(name, &yices_option)) {
      p = find_param(yices_option);
      if (p != PARAM_UNKNOWN) {
        assert(0 <= p && p < NUM_PARAMETERS);
        if (! yices_get_option(g, p)) {
          unsupported_option();
        }
      } else {
        unsupported_option();
      }
    } else {
      unsupported_option();
    }
    break;
  }

  flush_out();
}


/*
 * Check whether smtlib_version is set and if so print it
 */
static void show_smtlib_version(const smt2_globals_t *g) {
  switch (g->smtlib_version) {
  case 2000:
    print_kw_symbol_pair(":smt-lib-version", "2.0");
    break;

  case 2500:
    print_kw_symbol_pair(":smt-lib-version", "2.5");
    break;

  case 2600:
    print_kw_symbol_pair(":smt-lib-version", "2.6");
    break;

  default:
    print_kw_symbol_pair(":smt-lib-version", "unknown");
    break;
  }
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
  case SMT2_KW_ALL_STATISTICS:
    show_statistics(&__smt2_globals);
    break;

  case SMT2_KW_ASSERTION_STACK_LEVELS:
    print_kw_uint64_pair(name, __smt2_globals.stack.levels);
    break;

  case SMT2_KW_AUTHORS:
    print_kw_string_pair(name, yices_authors);
    break;

  case SMT2_KW_ERROR_BEHAVIOR:
    print_kw_symbol_pair(name, error_behavior);
    break;

  case SMT2_KW_NAME:
    print_kw_string_pair(name, yices_name);
    break;

  case SMT2_KW_REASON_UNKNOWN:
    explain_unknown_status(&__smt2_globals);
    break;

  case SMT2_KW_VERSION:
    print_kw_string_pair(name, yices_version);
    break;

  case SMT2_KW_SMT_LIB_VERSION:
    show_smtlib_version(&__smt2_globals);
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

static bool is_good_var_list(smt2_globals_t *g, aval_t avalue) {
  attr_list_t* d = aval_list(g->avtbl, avalue);
  uint32_t n = d->nelems;
  for (uint32_t i=0; i<n; i++) {
    aval_t vi = d->data[i];
    if (aval_tag(g->avtbl, vi) != ATTR_SYMBOL) return false;
    char* s = aval_symbol(g->avtbl, vi);
    if (yices_get_term_by_name(s) == NULL_TERM) return false;
  }
  return true;
}


/*
 * Attempt to convert value to a parameter value:
 * - value is an attribute value (SMT2 style)
 * - if this can't be done, store PARAM_ERROR in param_val
 * - avalue can be negative here.
 */
static void aval2param_val(smt2_globals_t *g, aval_t avalue, param_val_t *param_val) {
  rational_t *rational;
  char* symbol;

  if (avalue < 0) {
    param_val->tag = PARAM_VAL_ERROR;
    return;
  }

  switch (aval_tag(g->avtbl, avalue)) {
  case ATTR_RATIONAL:
    rational = aval_rational(g->avtbl, avalue);
    param_val->tag = PARAM_VAL_RATIONAL;
    param_val->val.rational = rational;
    break;

  case ATTR_SYMBOL:
    symbol = aval_symbol(g->avtbl, avalue);
    // We use the SMT2 conventions here: True/False are capitalized
    // NO THEY ARE NOT
    if (strcmp(symbol, "true") == 0) {
      param_val->tag = PARAM_VAL_TRUE;
    } else if (strcmp(symbol, "false") == 0) {
      param_val->tag = PARAM_VAL_FALSE;
    } else {
      param_val->tag = PARAM_VAL_SYMBOL;
      param_val->val.symbol = symbol;
    }
    break;

  case ATTR_STRING:
  case ATTR_BV:
  case ATTR_LIST: {
    if (is_good_var_list(g, avalue)) {
      param_val->tag       = PARAM_VAL_TERMS;
      param_val->val.terms = &g->var_order;
      attr_list_t* d = aval_list(g->avtbl, avalue);
      uint32_t n = d->nelems;
      for (uint32_t i=0; i<n; i++) {
        aval_t vi = d->data[i];
        assert(aval_tag(g->avtbl, vi) == ATTR_SYMBOL);
        char* s = aval_symbol(g->avtbl, vi);
        ivector_push(param_val->val.terms, yices_get_term_by_name(s));
      }
    } else {
      param_val->tag = PARAM_VAL_ERROR;
    }
    break;
  }

  case ATTR_DELETED:
    freport_bug(g->err, "smt2_commands: attribute deleted");
    break;
  }
}

static void yices_set_option(smt2_globals_t *g, const char *param, const param_val_t *val) {
  bool tt;
  int32_t n;
  double x;
  branch_t b;
  ef_gen_option_t gen;
  ivector_t* terms;
  char* reason;
  context_t *context;
  bool unsupported;   //keep track of those we punt on

  unsupported = false;
  reason = NULL;

  switch (find_param(param)) {
  case PARAM_VAR_ELIM:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters.var_elim = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_variable_elimination(context);
        } else {
          disable_variable_elimination(context);
        }
      }
    }
    break;

  case PARAM_ARITH_ELIM:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters.arith_elim = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_arith_elimination(context);
        } else {
          disable_arith_elimination(context);
        }
      }
    }
    break;

  case PARAM_BVARITH_ELIM:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters.bvarith_elim = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_bvarith_elimination(context);
        } else {
          disable_bvarith_elimination(context);
        }
      }
    }
    break;

  case PARAM_FLATTEN:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters.flatten_or = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_diseq_and_or_flattening(context);
        } else {
          disable_diseq_and_or_flattening(context);
        }
      }
    }
    break;

  case PARAM_LEARN_EQ:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters.eq_abstraction = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_eq_abstraction(context);
        } else {
          disable_eq_abstraction(context);
        }
      }
    }
    break;

  case PARAM_KEEP_ITE:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters.keep_ite = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_keep_ite(context);
        } else {
          disable_keep_ite(context);
        }
      }
    }
    break;

  case PARAM_FAST_RESTARTS:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->parameters.fast_restart = tt;
    }
    break;

  case PARAM_C_THRESHOLD:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.c_threshold = n;
    }
    break;

  case PARAM_C_FACTOR:
    if (param_val_to_factor(param, val, &x, &reason)) {
      g->parameters.c_factor = x;
    }
    break;

  case PARAM_D_THRESHOLD:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.d_threshold = n;
    }
    break;

  case PARAM_D_FACTOR:
    if (param_val_to_factor(param, val, &x, &reason)) {
      g->parameters.d_factor = x;
    }
    break;

  case PARAM_R_THRESHOLD:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.r_threshold = n;
    }
    break;

  case PARAM_R_FRACTION:
    if (param_val_to_ratio(param, val, &x, &reason)) {
      g->parameters.r_fraction = x;
    }
    break;

  case PARAM_R_FACTOR:
    if (param_val_to_factor(param, val, &x, &reason)) {
      g->parameters.r_factor = x;
    }
    break;

  case PARAM_VAR_DECAY:
    if (param_val_to_ratio(param, val, &x, &reason)) {
      g->parameters.var_decay = x;
    }
    break;

  case PARAM_RANDOMNESS:
    if (param_val_to_ratio(param, val, &x, &reason)) {
      g->parameters.randomness = x;
    }
    break;

  case PARAM_RANDOM_SEED:
    if (param_val_to_int32(param, val, &n, &reason)) {
      g->parameters.random_seed = (uint32_t) n;
    }
    break;

  case PARAM_BRANCHING:
    if (param_val_to_branching(param, val, &b, &reason)) {
      g->parameters.branching = b;
    }
    break;

  case PARAM_CLAUSE_DECAY:
    if (param_val_to_ratio(param, val, &x, &reason)) {
      g->parameters.clause_decay = x;
    }
    break;

  case PARAM_CACHE_TCLAUSES:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->parameters.cache_tclauses = tt;
    }
    break;

  case PARAM_TCLAUSE_SIZE:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.tclause_size = n;
    }
    break;

  case PARAM_DYN_ACK:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->parameters.use_dyn_ack = tt;
    }
    break;

  case PARAM_DYN_BOOL_ACK:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->parameters.use_bool_dyn_ack = tt;
    }
    break;

  case PARAM_OPTIMISTIC_FCHECK:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->parameters.use_optimistic_fcheck = tt;
    }
    break;

  case PARAM_MAX_ACK:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.max_ackermann = n;
    }
    break;

  case PARAM_MAX_BOOL_ACK:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.max_boolackermann = n;
    }
    break;

  case PARAM_AUX_EQ_QUOTA:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.aux_eq_quota = n;
    }
    break;

  case PARAM_AUX_EQ_RATIO:
    if (param_val_to_posfloat(param, val, &x, &reason)) {
      g->parameters.aux_eq_ratio = x;
    }
    break;

  case PARAM_DYN_ACK_THRESHOLD:
    if (param_val_to_pos16(param, val, &n, &reason)) {
      g->parameters.dyn_ack_threshold = (uint16_t) n;
    }
    break;

  case PARAM_DYN_BOOL_ACK_THRESHOLD:
    if (param_val_to_pos16(param, val, &n, &reason)) {
      g->parameters.dyn_bool_ack_threshold = (uint16_t) n;
    }
    break;

  case PARAM_MAX_INTERFACE_EQS:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.max_interface_eqs = n;
    }
    break;

  case PARAM_EAGER_LEMMAS:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters.splx_eager_lemmas = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_splx_eager_lemmas(context);
        } else {
          disable_splx_eager_lemmas(context);
        }
      }
    }
    break;

  case PARAM_SIMPLEX_PROP:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->parameters.use_simplex_prop = tt;
    }
    break;

  case PARAM_SIMPLEX_ADJUST:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->parameters.adjust_simplex_model = tt;
    }
    break;

  case PARAM_PROP_THRESHOLD:
    if (param_val_to_nonneg32(param, val, &n, &reason)) {
      g->parameters.max_prop_row_size = n;
    }
    break;

  case PARAM_BLAND_THRESHOLD:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.bland_threshold = n;
    }
    break;

  case PARAM_ICHECK:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ctx_parameters. splx_periodic_icheck = tt;
      context = g->ctx;
      if (context != NULL) {
        if (tt) {
          enable_splx_periodic_icheck(context);
        } else {
          disable_splx_periodic_icheck(context);
        }
      }
    }
    break;

  case PARAM_ICHECK_PERIOD:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.integer_check_period = n;
    }
    break;

  case PARAM_MAX_UPDATE_CONFLICTS:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.max_update_conflicts = n;
    }
    break;

  case PARAM_MAX_EXTENSIONALITY:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.max_extensionality = n;
    }
    break;

  case PARAM_EF_FLATTEN_IFF:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ef_client.ef_parameters.flatten_iff = tt;
    }
    break;

  case PARAM_EF_FLATTEN_ITE:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ef_client.ef_parameters.flatten_ite = tt;
    }
    break;

  case PARAM_EF_GEN_MODE:
    if (param_val_to_genmode(param, val, &gen, &reason)) {
      g->ef_client.ef_parameters.gen_mode = gen;
    }
    break;

  case PARAM_EF_MAX_SAMPLES:
    if (param_val_to_nonneg32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.max_samples = n;
    }
    break;

  case PARAM_EF_MAX_ITERS:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.max_iters = n;
    }
    break;

  case PARAM_EF_MAX_LEMMAS_PER_ROUND:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.max_numlearnt_per_round = n;
    }
    break;

  case PARAM_EMATCH_EN:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->ef_client.ef_parameters.ematching = tt;
    }
    break;

  case PARAM_EMATCH_INST_PER_ROUND:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_inst_per_round = n;
    }
    break;

  case PARAM_EMATCH_INST_PER_SEARCH:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_inst_per_search = n;
    }
    break;

  case PARAM_EMATCH_INST_TOTAL:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_inst_total = n;
    }
    break;

  case PARAM_EMATCH_ROUNDS_PER_SEARCH:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_rounds_per_search = n;
    }
    break;

  case PARAM_EMATCH_SEARCH_TOTAL:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_search_total = n;
    }
    break;

  case PARAM_EMATCH_TRIAL_FDEPTH:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_exec_max_fdepth = n;
    }
    break;

  case PARAM_EMATCH_TRIAL_VDEPTH:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_exec_max_vdepth = n;
    }
    break;

  case PARAM_EMATCH_TRIAL_FAPPS:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_exec_max_fapps = n;
    }
    break;

  case PARAM_EMATCH_TRIAL_MATCHES:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_exec_max_matches = n;
    }
    break;

  case PARAM_EMATCH_CNSTR_EPSILON:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_cnstr_epsilon = n;
    }
    break;

  case PARAM_EMATCH_CNSTR_ALPHA:
    if (param_val_to_ratio(param, val, &x, &reason)) {
      g->ef_client.ef_parameters.ematch_cnstr_alpha = x;
    }
    break;

  case PARAM_EMATCH_TERM_EPSILON:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->ef_client.ef_parameters.ematch_term_epsilon = n;
    }
    break;

  case PARAM_EMATCH_TERM_ALPHA:
    if (param_val_to_ratio(param, val, &x, &reason)) {
      g->ef_client.ef_parameters.ematch_term_alpha = x;
    }
    break;

  case PARAM_EMATCH_CNSTR_MODE:
    if (param_val_to_ematchmode(param, val, (iterate_kind_t *)&n, &reason)) {
      g->ef_client.ef_parameters.ematch_cnstr_mode = n;
    }
    break;

  case PARAM_EMATCH_TERM_MODE:
    if (param_val_to_ematchmode(param, val, (iterate_kind_t *)&n, &reason)) {
      g->ef_client.ef_parameters.ematch_term_mode = n;
    }
    break;

  case PARAM_MCSAT_NRA_MGCD:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->mcsat_options.nra_mgcd = tt;
      context = g->ctx;
      if (context != NULL) {
        context->mcsat_options.nra_mgcd = tt;
      }
    }
    break;

  case PARAM_MCSAT_NRA_NLSAT:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->mcsat_options.nra_nlsat = tt;
      context = g->ctx;
      if (context != NULL) {
        context->mcsat_options.nra_nlsat = tt;
      }
    }
    break;

  case PARAM_MCSAT_NRA_BOUND:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->mcsat_options.nra_bound = tt;
      context = g->ctx;
      if (context != NULL) {
        context->mcsat_options.nra_bound = tt;
      }
    }
    break;

  case PARAM_MCSAT_NRA_BOUND_MIN:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->mcsat_options.nra_bound_min = n;
      context = g->ctx;
      if (context != NULL) {
        context->mcsat_options.nra_bound_min = n;
      }
    }
    break;

  case PARAM_MCSAT_NRA_BOUND_MAX:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->mcsat_options.nra_bound_max = n;
      context = g->ctx;
      if (context != NULL) {
        context->mcsat_options.nra_bound_max = n;
      }
    }
    break;

  case PARAM_MCSAT_BV_VAR_SIZE:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->mcsat_options.bv_var_size = n;
      context = g->ctx;
      if (context != NULL) {
        context->mcsat_options.bv_var_size = n;
      }
    }
    break;

  case PARAM_MCSAT_RAND_DEC_FREQ:
    if (param_val_to_ratio(param, val, &x, &reason)) {
      g->parameters.randomness = x;
    }
    break;

  case PARAM_MCSAT_RAND_DEC_SEED:
    if (param_val_to_pos32(param, val, &n, &reason)) {
      g->parameters.random_seed = n;
    }
    break;

  case PARAM_MCSAT_VAR_ORDER:
    if (param_val_to_terms(param, val, &terms, &reason)) {
      context = g->ctx;
      if (context != NULL) {
        ivector_copy(&context->mcsat_var_order, terms->data, terms->size);
      }
    }
    break;

  case PARAM_MCSAT_L2O:
    if (param_val_to_bool(param, val, &tt, &reason)) {
      g->mcsat_options.l2o = tt;
      context = g->ctx;
      if (context != NULL) {
        context->mcsat_options.l2o = tt;
      }
      g->parameters.mcsat_l2o = tt;
    }
    break;

  case PARAM_UNKNOWN:
  default:
    unsupported = true;
    break;
  }

  if (unsupported) {
    unsupported_option();
    flush_out();
  } else if (reason != NULL) {
    print_error("in (set-option "YICES_SMT2_PREFIX"%s ...): %s", param, reason);
  } else {
    report_success();
  }
}


/*
 * Set an option:
 * - name = option name (keyword)
 * - value = value (either stored in:
 *
 *  the parameters struct
 *  the ef_parametrs struct, or
 *  the attribute_value table)
 *
 * SMT2 allows the syntax (set-option :keyword). In such a case,
 * this function is called with value = NULL_VALUE (i.e., -1).
 */
void smt2_set_option(const char *name, aval_t value) {
  smt2_globals_t *g;
  smt2_keyword_t kw;
  uint32_t n;
  const char* yices_option;
  param_val_t param_val;

  g = &__smt2_globals;

  n = kwlen(name);
  kw = smt2_string_to_keyword(name, n);

  switch (kw) {
  case SMT2_KW_DIAGNOSTIC_OUTPUT:
    // required
    set_error_file(g, name, value);
    break;

  case SMT2_KW_GLOBAL_DECLARATIONS:
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->global_decls);
    }
    break;

  case SMT2_KW_PRINT_SUCCESS:
    // required
    set_boolean_option(g, name, value, &g->print_success);
    break;

  case SMT2_KW_PRODUCE_ASSIGNMENTS:
    // optional: if true, get-assignment can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_assignments);
    }
    break;

  case SMT2_KW_PRODUCE_MODELS:
    // optional: if true, get-value can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_models);
    }
    break;

  case SMT2_KW_RANDOM_SEED:
    // optional
    set_uint32_option(g, name, value, &g->random_seed);
    break;

  case SMT2_KW_REGULAR_OUTPUT:
    // required
    set_output_file(g, name, value);
    break;

  case SMT2_KW_VERBOSITY:
    // optional
    set_verbosity(g, name, value);
    break;

  case SMT2_KW_DUMP_MODELS:
    set_boolean_option(g, name, value, &g->dump_models);
    break;

  case SMT2_KW_TIMEOUT:
    set_uint32_option(g, name, value, &g->timeout);
    break;

  case SMT2_KW_PRODUCE_UNSAT_ASSUMPTIONS:
    // optional: if true, get-unsat-assumptions can be used
    if (option_can_be_set(name)) {
      set_unsat_assumption_option(g, name, value);
    }
    break;

  case SMT2_KW_PRODUCE_UNSAT_CORES:
    // optional: if true,  get-unsat-cores can be used
    if (option_can_be_set(name)) {
      set_unsat_core_option(g, name, value);
    }
    break;

  case SMT2_KW_PRODUCE_UNSAT_MODEL_INTERPOLANTS:
    // optional: if true, get-unsat-model-interpolant can be used
    if (option_can_be_set(name)) {
      set_unsat_model_interpolants_option(g, name, value);
    }
    break;

  case SMT2_KW_EXPAND_DEFINITIONS:
  case SMT2_KW_INTERACTIVE_MODE:
  case SMT2_KW_PRODUCE_ASSERTIONS:
  case SMT2_KW_PRODUCE_PROOFS:
  case SMT2_KW_REPRODUCIBLE_RESOURCE_LIMIT:
    unsupported_option();
    flush_out();
    break;

  default:
    // may be a Yices option
    if (is_yices_option(name, &yices_option)) {
      aval2param_val(g, value, &param_val);
      yices_set_option(g, yices_option, &param_val);
    } else {
      unsupported_option();
      flush_out();
    }
    break;
  }
}


/*
 * Set some info field
 * - same conventions as set_option
 */
void smt2_set_info(const char *name, aval_t value) {
  smt2_globals_t *g;
  smt2_keyword_t kw;
  uint32_t n, version;

  g = &__smt2_globals;

  n = kwlen(name);
  kw = smt2_string_to_keyword(name, n);

  switch (kw) {
  case SMT2_KW_ALL_STATISTICS:
  case SMT2_KW_ASSERTION_STACK_LEVELS:
  case SMT2_KW_AUTHORS:
  case SMT2_KW_ERROR_BEHAVIOR:
  case SMT2_KW_NAME:
  case SMT2_KW_REASON_UNKNOWN:
  case SMT2_KW_VERSION:
    print_error("can't overwrite %s", name);
    break;

  case SMT2_KW_SMT_LIB_VERSION:
    // quick hack to switch parser if 2.5 is selected
    if (g->smtlib_version != 0) {
      print_error("can't set :smt-lib-version twice");
    } else if (aval_is_known_version(g->avtbl, value, &version)) {
      assert(version == 2000 || version == 2500 || version == 2600);
      g->smtlib_version = version;
      if (version >= 2500) {
        smt2_lexer_activate_two_dot_five();
      }
      report_success();
    } else {
      print_error("unsupported :smt-lib-version");
    }
    break;

  default:
    add_info(g, name, value);
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
  context_arch_t arch;

  if (__smt2_globals.logic_code != SMT_UNKNOWN) {
    print_error("the logic is already set");
    return;
  }

  code = smt_logic_code(name);
  if (code == SMT_UNKNOWN) {
    print_error("unknown logic: %s", name);
    return;
  }

  if (logic_is_supported_by_ef(code)) {
    __smt2_globals.efmode = true;
    arch = ef_arch_for_logic(code);
  } else if (logic_is_supported(code)) {
    __smt2_globals.efmode = false;
    arch = arch_for_logic(code);
  } else {
    print_error("logic %s is not supported", name);
    return;
  }

  if (! logic_is_official(code)) {
    trace_printf(__smt2_globals.tracer, 2, "(Warning: logic %s is not an official SMT-LIB logic)\n", name);
  }

  // if export_to_dimacs: fail if the logic is not QF_BV
  if (__smt2_globals.export_to_dimacs && code != QF_BV) {
    print_error("can't generate DIMACS file for logic %s", name);
    return;
  }

  // if mcsat was requested, check whether the logic is supported by the MCSAT solver
  if (__smt2_globals.mcsat && !logic_is_supported_by_mcsat(code)) {
    print_error("logic %s is not supported by the mcsat solver", name);
    return;
  }

  // if the logic requires MCSAT, check whether this was compiled with MCSAT support
  if (logic_requires_mcsat(code) && !yices_has_mcsat()) {
    print_error("logic %s is not supported since yices was not built with mcsat support", name);
    return;
  }

  // in efmode : can't use the mcsat solver and must not be incremental
  if (__smt2_globals.efmode) {
    if (__smt2_globals.mcsat) {
      print_error("the mcsat solver does not support quantifiers");
      return;
    }
    if (! __smt2_globals.benchmark_mode) {
      print_error("the exists/forall solver does not work in incremental mode");
      return;
    }
    if (__smt2_globals.produce_unsat_cores || __smt2_globals.produce_unsat_assumptions) {
      print_error("the exists/forall solver does not support unsat cores");
      return;
    }
  }

  // if unsat cores or unsat assumptions are requested, we can't use the mcsat solver
  if (__smt2_globals.produce_unsat_cores || __smt2_globals.produce_unsat_assumptions) {
    if (__smt2_globals.mcsat) {
      // Allow unsat cores with MCSAT if model interpolation is enabled
      if (!__smt2_globals.mcsat_options.model_interpolation) {
        print_error("the mcsat solver does not support unsat cores without model interpolation");
        return;
      }
    }
    if (arch == CTX_ARCH_MCSAT) {
      // Allow unsat cores with MCSAT architecture if model interpolation is enabled
      if (!__smt2_globals.mcsat_options.model_interpolation) {
        print_error("unsat cores are not supported in logic %s with MCSAT without model interpolation", name);
        return;
      }
    }
  }

  smt2_lexer_activate_logic(code);
  __smt2_globals.logic_code = code;
  __smt2_globals.logic_name = clone_string(name);
  string_incref(__smt2_globals.logic_name);

  // Set model_interpolation if unsat cores are enabled and architecture is MCSAT
  if ((__smt2_globals.produce_unsat_cores || __smt2_globals.produce_unsat_assumptions) && 
      (arch == CTX_ARCH_MCSAT || __smt2_globals.mcsat)) {
    __smt2_globals.mcsat_options.model_interpolation = true;
  }

  /*
   * In incremental mode: initialize the context
   */
  if (! __smt2_globals.benchmark_mode) {
    init_smt2_context(&__smt2_globals);
    init_search_parameters(&__smt2_globals);
    save_ctx_params(&__smt2_globals.ctx_parameters, __smt2_globals.ctx);
  } else {
    // in benchmark mode (or exists/forall) set the parameters to defaults for the logic
    // the context is not initialized yet
    default_ctx_params(&__smt2_globals.ctx_parameters, code, arch, CTX_MODE_ONECHECK);
    yices_set_default_params(&__smt2_globals.parameters, code, arch, CTX_MODE_ONECHECK);
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

  g = &__smt2_globals;

  g->stats.num_pop ++;
  g->stats.num_commands ++;

  tprint_calls("pop", g->stats.num_pop);

  if (check_logic()) {
    if (g->benchmark_mode) {
      print_error("pop is not allowed in non-incremental mode");
    } else if (n == 0) {
      // do nothing
      report_success();
    } else {
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
 * - special is true if t is a :named assertion
 */
void smt2_assert(term_t t, bool special) {
  smt2_globals_t *g;

  g = &__smt2_globals;

  g->stats.num_assert ++;
  g->stats.num_commands ++;
  tprint_calls("assert", g->stats.num_assert);

  if (check_logic()) {
    if (yices_term_is_bool(t)) {
      if (g->benchmark_mode) {
        /*
         * NOT INCREMENTAL
         */
        if (g->efmode && g->ef_client.efdone) {
          print_error("more assertions are not allowed after solving");
        } else if (g->frozen) {
          print_error("assertions are not allowed after (check-sat) in non-incremental mode");
        } else {
          /*
	   * Otherwise, if produce unsat core is set and t is special,
           * we just skip it. The term is stored in the named_asserts table
           * and will be treated as an assumption when check-sat is called.
           */
          if (!special || !g->produce_unsat_cores) {
            add_delayed_assertion(g, t);
          } else {
	    assert(!g->efmode);
            trace_printf(g->tracer, 20, "(skipping named assertion)\n");
          }
          report_success();
        }

      } else {
        /*
         * INCREMENTAL
         */
        cleanup_context(g);
        if (!special || !g->produce_unsat_cores) {
          add_assertion(g, t);
        } else {
          trace_printf(g->tracer, 20, "(skipping named assertion)\n");
          report_success();
        }
      }
    } else {
      // not a Boolean term
      print_error("type error in assert: Boolean term required");
    }
  }
}



#ifdef THREAD_SAFE

/*
 * PROVISIONAL CODE FOR TESTING MULTIPLE SOLVERS & CONTEXTS
 * IN SEPARATE THREADS
 */

static yices_thread_result_t YICES_THREAD_ATTR check_delayed_assertions_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;
  smt2_globals_t *g = (smt2_globals_t *)tdata->extra;

  g->out = output;   // /tmp/check_delayed_assertions_thread_<thread index>.txt
  g->err = output;   // /tmp/check_delayed_assertions_thread_<thread index>.txt

  check_delayed_assertions(g, /*report=*/false);

  return yices_thread_exit();
}

static smt_status_t get_status_from_globals(smt2_globals_t *g) {
  if (g->trivially_unsat) {
    return STATUS_UNSAT;
  } else if (g->trivially_sat) {
    return STATUS_SAT;
  } else {
    assert(g->ctx);
    return yices_context_status(g->ctx);
  }
}

/*
 * Test multi-threaded code:
 * - g->nthreads = number of threads to run
 */
static void check_delayed_assertions_mt(smt2_globals_t *g) {
  bool success;
  uint32_t i, n;
  bool verbose;

  n = g->nthreads;
  assert(n > 0);

  verbose = g->verbosity > 0;
    
  smt2_globals_t *garray =  (smt2_globals_t *) safe_malloc(n * sizeof(smt2_globals_t));
  for(i = 0; i < n; i++) {
    garray[i] = __smt2_globals;  // just copy them for now.
    garray[i].tracer = NULL;     // only main thread can use this.
  }
  launch_threads(n, garray, sizeof(smt2_globals_t), "check_delayed_assertions_thread", check_delayed_assertions_thread, verbose);
  if (verbose)
    fprintf(stderr, "All threads finished. Now computing check_delayed_assertions in main thread.\n");
  check_delayed_assertions(g, /*report=*/true);

  //could check that they are all OK

  smt_status_t main_answer = get_status_from_globals(g);
  success = true;
  for (i = 0; i < n; i++) {
    smt_status_t answer = get_status_from_globals(garray + i);
    if (answer != main_answer) {
      success = false;
    }
    //free the model if there is one, and free the context.
    //IAM: valgrind says there is no leak here. This is puzzling.
  }
  if (verbose)
    fprintf(stderr,
	    success ? "SUCCESS: All threads agree.\n" : "FAILURE: Threads disagree.\n");
  safe_free(garray);
}
#endif



/*
 * Check satisfiability of the current set of assertions
 */
void smt2_check_sat(void) {
  __smt2_globals.stats.num_check_sat ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("check-sat", __smt2_globals.stats.num_check_sat);

  if (check_logic()) {
    if (__smt2_globals.benchmark_mode) {
      /*
       * Non incremental
       */
      if (__smt2_globals.efmode) {
        efsolve_cmd(&__smt2_globals);
      } else if (__smt2_globals.frozen) {
        print_error("multiple calls to (check-sat) are not allowed in non-incremental mode");
      } else if (__smt2_globals.produce_unsat_cores) {
        delayed_assertions_unsat_core(&__smt2_globals);
      } else {
        // show_delayed_assertions(&__smt2_globals);
#ifndef THREAD_SAFE
        check_delayed_assertions(&__smt2_globals, /*report=*/true);
#else
        if (__smt2_globals.nthreads == 0) {
          check_delayed_assertions(&__smt2_globals, /*report=*/true);
        } else {
          check_delayed_assertions_mt(&__smt2_globals);
        }
#endif
      }
    } else {
      /*
       * Incremental
       */
      if (__smt2_globals.produce_unsat_cores) {
        ctx_unsat_core(&__smt2_globals);
      } else {
        ctx_check_sat(&__smt2_globals);
      }
    }
  }
}

/*
 * Check sat with assumptions:
 * - n = number of assumptions
 * - a = array of assumptions
 * Each assumption is represented as a signed symbol,
 * i.e., a pair symbol name/polarity.
 */
void smt2_check_sat_assuming(uint32_t n, signed_symbol_t *a) {
  __smt2_globals.stats.num_check_sat_assuming ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("check-sat-assuming", __smt2_globals.stats.num_check_sat_assuming);

  if (check_logic()) {
    if (__smt2_globals.produce_unsat_cores) {
      print_error("check-sat-assuming is not supported when :produce-unsat-cores is true");
    } else if (__smt2_globals.benchmark_mode) {
      if (__smt2_globals.efmode) {
        print_error("the exists/forall solver does not support check-sat with assumptions");
      } else if (__smt2_globals.frozen) {
        print_error("multiple calls to (check-sat) are not allowed in non-incremental mode");
      } else {
        check_delayed_assertions_assuming(&__smt2_globals, n, a);
      }
    } else {
      ctx_check_sat_assuming(&__smt2_globals, n, a);
    }
  }
}

/*
 * Check sat with model as assumptions:
 * - n = number of assumptions
 * - vars = array of variables
 * - values = array of values
 */
void smt2_check_sat_assuming_model(uint32_t n, const term_t vars[], const term_t values[]) {
  __smt2_globals.stats.num_check_sat_assuming_model ++;
  __smt2_globals.stats.num_commands ++;
  tprint_calls("check-sat-assuming-model", __smt2_globals.stats.num_check_sat_assuming_model);

  if (check_logic()) {
    if (!mcsat_enabled(&__smt2_globals)) {
      print_error("check-sat-assuming-model is only supported in MCSAT");
    } else if (__smt2_globals.benchmark_mode) {
      if (__smt2_globals.efmode) {
        print_error("the exists/forall solver does not support check-sat with assumptions");
      } else if (__smt2_globals.frozen) {
        print_error("multiple calls to (check-sat) are not allowed in non-incremental mode");
      } else {
        check_delayed_assertions_assuming_model(&__smt2_globals, n, vars, values);
      }
    } else {
      ctx_check_sat_assuming_model(&__smt2_globals, n, vars, values);
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
	done = true;
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
	done = true;
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
    save_name_for_model(&__smt2_globals, name);

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
      done = true;
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
	done = true;
        return;
      }
    }
    yices_set_term_name(t, name);
    save_term_name(&__smt2_globals, name);

    report_success();
  }
}


/*
 * Show the model if any
 */
void smt2_get_model(void) {
  smt2_pp_t printer;
  smt2_model_t smt2_mdl;
  model_t *mdl;

  if (check_logic()) {
    if (__smt2_globals.efmode) {
      mdl = get_ef_model(&__smt2_globals);
    } else {
      mdl = get_model(&__smt2_globals);
    }
    if (mdl == NULL) return;

    init_pretty_printer(&printer, &__smt2_globals);
    if (__smt2_globals.clean_model_format) {
      smt2_pp_full_model(&printer, mdl);
    } else {
      init_smt2_model(&smt2_mdl, mdl);
      build_smt2_model(&__smt2_globals, &smt2_mdl);
      print_smt2_model(&printer, &smt2_mdl);
      delete_smt2_model(&smt2_mdl);
    }
    delete_smt2_pp(&printer, true);
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
 * Reset all assertions
 * - delete all assertions, terms, types, and declarations
 * - the standard allows (reset-assertions) even if no logic is set.
 * - in the latter case, we do nothing and report success. There's no
 *   initialized context until the logic is set.
 */
void smt2_reset_assertions(void) {
  smt2_globals_t *g;

  g = &__smt2_globals;
  if (g->benchmark_mode) {
    print_error("reset-assertions is not allowed in non-incremental mode");
  } else {
    if (g->logic_code !=  SMT_UNKNOWN) {
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

      /*
       * If global_declations is set, then the name stacks
       * and the named_bools stack are empty. The reset
       * functions do nothing.
       *
       * We remove the named_assertions whether or not
       * global_declarations is set.
       */
      reset_smt2_name_stack(&g->term_names);
      reset_smt2_name_stack(&g->type_names);
      reset_smt2_name_stack(&g->macro_names);

      reset_named_term_stack(&g->named_bools);
      reset_named_term_stack(&g->named_asserts);

      reset_string_vector(&g->model_term_names);

      if (g->unsat_core != NULL) {
        free_assumptions(g->unsat_core);
        g->unsat_core = NULL;
      }
      if (g->unsat_assumptions != NULL) {
        free_assumptions(g->unsat_assumptions);
        g->unsat_assumptions = NULL;
      }

      reset_etk_queue(&g->token_queue);
      ivector_reset(&g->token_slices);
      ivector_reset(&g->val_vector);

      /*
       * Reset the internal name tables, unless global_decls is set
       */
      if (!g->global_decls) {
        yices_reset_tables();
      }

      // build a fresh empty context
      init_smt2_context(g);
    }

    report_success();
  }
}


/*
 * Full reset: we ensure that all flags and options that are set on
 * the command line are preserved.
 */
void smt2_reset_all(void) {
  bool benchmark, print_success, clean_format, bvdecimal;
  uint32_t timeout, verbosity;

  benchmark = __smt2_globals.benchmark_mode;
  clean_format = __smt2_globals.clean_model_format;
  bvdecimal = __smt2_globals.bvconst_in_decimal;
  timeout = __smt2_globals.timeout;
  print_success = __smt2_globals.print_success;
  verbosity = __smt2_globals.verbosity;

  delete_smt2_globals(&__smt2_globals);
  delete_attr_vtbl(&avtbl); // must be done last
  yices_reset_tables();

  init_smt2(benchmark, timeout, print_success);
  smt2_set_verbosity(verbosity);
  if (! clean_format) smt2_force_smt2_model_format();
  if (bvdecimal) smt2_force_bvdecimal_format();
  smt2_lexer_reset_logic();

  report_success();
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
      clone = clone_string(name);
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
  ptr_hmap_pair_t *r;
  term_t x;

  r = ptr_hmap_get(&__smt2_globals.term_patterns, t);
  if (r->val == NULL) {
    r->val = safe_malloc(sizeof(ivector_t));
    init_ivector(r->val, 0);
  }

#if 0
  printf("adding pattern:\n");
  printf("  term: ");
  yices_pp_term(stdout, t, 120, 1, 0);
  printf("  pattern: ");
  yices_pp_term_array(stdout, n, p, 120, 1, 0, 1);
#endif

  if (n == 1) {
    x = p[0];
  } else {
    x = yices_tuple(n, p);
  }
  ivector_push(r->val, x);
}

/*
 * Enables the mcsat solver.
 */
void smt2_enable_mcsat(void) {
  __smt2_globals.mcsat = true;
}
