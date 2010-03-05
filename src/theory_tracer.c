/*
 * DEBUGGING HELP: TRACE THEORY CONFLICTS/PROPAGATION/LEMMAS
 */

#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <inttypes.h>

#include "memalloc.h"
#include "int_vectors.h"
#include "extended_rationals.h"
#include "int_hash_sets.h"
#include "egraph_types.h"
#include "idl_floyd_warshall.h"
#include "rdl_floyd_warshall.h"
#include "simplex.h"
#include "bvsolver.h"
#include "fun_solver.h"
#include "solver_printer.h"
#include "theory_tracer.h"



/*
 * Which arithmetic solver is used
 */
typedef enum {
  NO_SOLVER,
  SPLX_SOLVER,
  IFW_SOLVER,
  RFW_SOLVER,
} arith_solver_type_t;


/*
 * Global variables:
 * - trace_file = output stream
 * - context = context
 * - core
 * - egraph
 * - arith_solver
 * - bit vector solver
 * - arrady solver
 */
static FILE *trace_file = NULL;
static char *file_name = NULL;

static context_t *context = NULL;
static smt_core_t *core = NULL;
static egraph_t *egraph = NULL;
static void *arith_solver = NULL;
static bv_solver_t *bv_solver = NULL;
static fun_solver_t *fun_solver = NULL;


static arith_solver_type_t arith_type;
static bool egraph_exists = false;
static bool shown_simplex = true;
static bool tracer_ready = false;

static ivector_t buffer;
static int_hset_t hset;


/*
 * Initialize internal variables:
 * - ctx = context (must be initialized so that tracer can determine
 *   which solvers are being used)
 * - file = trace file where all data is dumped
 * If file can't be opened, the function calls abort()
 */
void start_theory_tracer(context_t *ctx, char *file) {
  uint32_t n;

  trace_file = fopen(file, "w");
  if (trace_file == NULL) {
    perror(file);
    abort();
  }

  n = strlen(file);
  file_name = (char *) safe_malloc(n + 1);
  strcpy(file_name, file);

  init_ivector(&buffer, 10);
  init_int_hset(&hset, 0);

  context = ctx;
  core = ctx->core;
  egraph = ctx->egraph;
  arith_solver = ctx->arith_solver;

  egraph_exists = context_has_egraph(ctx);

  shown_simplex = true;
  arith_type = NO_SOLVER;
  if (context_has_arith_solver(ctx)) {
    if (context_has_idl_solver(ctx)) {
      arith_type = IFW_SOLVER; // IDL/Floyd-Warshall
    } else if (context_has_rdl_solver(ctx)) {
      arith_type = RFW_SOLVER; // RDL/Floyd-Warshall
    } else if (context_has_simplex_solver(ctx)) {
      arith_type = SPLX_SOLVER;
      shown_simplex = false;
    }
  }


  if (context_has_bv_solver(ctx)) {
    bv_solver = ctx->bv_solver;
  }

  if (context_has_fun_solver(ctx)) {
    fun_solver = ctx->fun_solver;
  }

  tracer_ready = true;
}


/*
 * Close the trace file and cleanup
 */
void end_theory_tracer(void) {
  safe_free(file_name);
  file_name = NULL;
  fclose(trace_file);
  delete_ivector(&buffer);
  delete_int_hset(&hset);
  tracer_ready = false;
}



/*
 * Return the trace file (NULL if it's not ready)
 */
FILE *trace_theory_file(void) {
  return tracer_ready ? trace_file : NULL;
}


/*
 * Print initial simplex tableau + fixed variables
 */
static void trace_simplex_tableau(void) {
  simplex_solver_t *splx;

  splx = (simplex_solver_t *) arith_solver;

  fprintf(trace_file, "\nSIMPLEX TABLEAU\n");
  print_simplex_matrix(trace_file, splx);
  fprintf(trace_file, "\nFIXED VARIABLES\n");
  print_fixed_var_vector(trace_file, &splx->vtbl, &splx->fvars);
  fprintf(trace_file, "\n================================================\n\n\n\n");

  shown_simplex = true;
}


/*
 * Print an atom
 */
static void trace_egraph_atom(atom_t *a) {
  eterm_t t;

  t = a->eterm;
  print_eterm(trace_file, egraph, t);
}

static void trace_idl_atom(void *a) {
  idl_solver_t *solver;
  idl_atom_t *atom;
  int32_t idx;

  solver = (idl_solver_t *) arith_solver;
  idx = atom2index(a);
  atom = solver->atoms.atoms + idx;
  fprintf(trace_file, "(<= (- i!%"PRId32" i!%"PRId32") %"PRId32")", atom->source, atom->target, atom->cost);
}

static void trace_rdl_atom(void *a) {
  rdl_solver_t *solver;
  rdl_atom_t *atom;
  int32_t idx;

  solver = (rdl_solver_t *) arith_solver;
  idx = rdl_atom2index(a);
  atom = solver->atoms.atoms + idx;

  fprintf(trace_file, "(<= (- z!%"PRId32" z!%"PRId32") ", atom->source, atom->target);
  q_print(trace_file, &atom->cost);
  fputc(')', trace_file);
}

static void trace_simplex_atom(void *a) {
  simplex_solver_t *solver;
  arith_atom_t *atom;
  int32_t idx;  

  solver = (simplex_solver_t *) arith_solver;
  idx = arithatom_tagged_ptr2idx(a);
  atom = arith_atom(&solver->atbl, idx);
  switch (tag_of_atom(atom)) {
  case GE_ATM:
    fputs("(>= ", trace_file);
    break;
  case LE_ATM:
    fputs("(<= ", trace_file);
    break;
  case EQ_ATM:
    fputs("(= ", trace_file);
    break;
  default:
    fputs("(BAD-ARITH-ATOM ", trace_file);
    break;
  }
  print_simplex_var(trace_file, solver, var_of_atom(atom));
  fputc(' ', trace_file);
  q_print(trace_file, bound_of_atom(atom));
  fputc(')', trace_file);  
}


static void trace_bv_atom(void *a) {
  bvatm_t *atom;
  int32_t id;

  id = bvatom_tagged_ptr2idx(a);
  atom = bv_solver->atbl.data + id;
  switch (bvatm_tag(atom)) {
  case BVEQ_ATM:
    fputs("(bveq ", trace_file);
    break;
  case BVUGE_ATM:
    fputs("(bvge ", trace_file);
    break;
  case BVSGE_ATM:
    fputs("(bvsge ", trace_file);
    break;
  default:
    fputs("(BAD-BV-ATOM ", trace_file);
    break;
  }
  print_bvsolver_var(trace_file, atom->left);
  fputc(' ', trace_file);
  print_bvsolver_var(trace_file, atom->right);
  fputc(')', trace_file);
}


/*
 * Print a monomial a * x for simplex
 */
static void trace_simplex_monomial(simplex_solver_t *solver, rational_t *a, thvar_t x) {
  if (x == const_idx) {
    q_print(trace_file, a);
  } else if (q_is_one(a)) {
    print_simplex_var(trace_file, solver, x);
  } else if (q_is_minus_one(a)) {
    fputs("(- ", trace_file);
    print_simplex_var(trace_file, solver, x);
    fputc(')', trace_file);
  } else {
    fputs("(* ", trace_file);
    q_print(trace_file, a);
    fputc(' ', trace_file);
    print_simplex_var(trace_file, solver, x);
    fputc(')', trace_file);
  }
}

/*
 * Print a row in the tableau
 */
static void trace_simplex_row(row_t *row) {
  simplex_solver_t *solver;
  uint32_t i, n, m;
  thvar_t x;

  solver = (simplex_solver_t *) arith_solver;
  fputs("(= ", trace_file);
  m = row->nelems;

  if (m == 0) {
    fputs("0", trace_file);
  } else {
    if (m > 1) {
      fputs("(+ ", trace_file);
    }
    n = row->size;  
    for (i=0; i<n; i++) {
      x = row->data[i].c_idx;
      if (x >= 0) {
	if (i > 0) fputc(' ', trace_file);
	trace_simplex_monomial(solver, &row->data[i].coeff, x);
      }
    }
    if (m > 1) {
      fputs(")", trace_file);
    }
  }
  fputs(" 0)", trace_file);
}



/*
 * Check whether x is a fixed variable in simplex solver
 */
static bool simplex_fixed_variable(simplex_solver_t *solver, thvar_t x) {
  int32_t l, u;

  l = arith_var_lower_index(&solver->vtbl, x);
  u = arith_var_upper_index(&solver->vtbl, x);
  return (l >= 0) && (u >= 0) && xq_eq(&solver->bstack.bound[l], &solver->bstack.bound[u]);
}

/*
 * Value of variable x
 */
static xrational_t *simplex_variable_value(simplex_solver_t *solver, thvar_t x) {
  return arith_var_value(&solver->vtbl, x);
}


/*
 * Print a set of fixed variables
 * - s = the set (closed)
 */
static void trace_simplex_fixed_variables(int_hset_t *s) {
  simplex_solver_t *solver;
  uint32_t i, n;
  thvar_t x;

  solver = (simplex_solver_t *) arith_solver;

  n = s->nelems;
  for (i=0; i<n; i++) {
    x = s->data[i];
    assert(simplex_fixed_variable(solver, x));
    fputs("  ", trace_file);
    print_simplex_var(trace_file, solver, x);
    fputs(" = ", trace_file);
    xq_print(trace_file, simplex_variable_value(solver, x));
    fputc('\n', trace_file);
  }
}

/*
 * Add all fixed variables of row to set s
 */
static void collect_fixed_vars_of_row(row_t *row, int_hset_t *s) {
  simplex_solver_t *solver;
  uint32_t i, n;
  thvar_t x;

  solver = (simplex_solver_t *) arith_solver;

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0 && simplex_fixed_variable(solver, x)) {
      int_hset_add(s, x);
    }
  }  
}



/*
 * Print a row but replace the fixed variables by their value
 */
static void trace_simplex_reduced_row(row_t *row) {
  simplex_solver_t *solver;
  uint32_t i, n;
  thvar_t x;
  xrational_t constant;

  solver = (simplex_solver_t *) arith_solver;
  xq_init(&constant);

  fputs("(= (+", trace_file);

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      if (simplex_fixed_variable(solver, x)) {
	xq_addmul(&constant, simplex_variable_value(solver, x), &row->data[i].coeff);
      } else {
	fputc(' ', trace_file);
	trace_simplex_monomial(solver, &row->data[i].coeff, x);
      }
    }
  }

  fputc(' ', trace_file);
  xq_print(trace_file, &constant);  

  fputs(") 0)", trace_file);
  xq_clear(&constant);
}


/*
 * Print the basic variable in row
 */
static void trace_simplex_basic_var(row_t *row) {
  simplex_solver_t *solver;
  uint32_t i, n;
  thvar_t x;

  solver = (simplex_solver_t *) arith_solver;
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0 && matrix_is_basic_var(&solver->matrix, x)) {
      fputs("Basic var: ", trace_file);
      print_simplex_var(trace_file, solver, x);
      return;
    }
  }

  fputs("No basic var", trace_file);
}

/*
 * Print bound of index k in the simplex solver
 */
static void trace_simplex_bound(int32_t k) {
  simplex_solver_t *solver;
  arith_bstack_t *bstack;

  solver = (simplex_solver_t *) arith_solver;
  bstack = &solver->bstack;
  if (arith_tag_get_type(bstack->tag[k]) == ATYPE_UB) {
    fputs("(<= ", trace_file);
  } else {
    fputs("(>= ", trace_file);
  }
  print_simplex_var(trace_file, solver, bstack->var[k]);
  fputc(' ', trace_file);
  xq_print(trace_file, bstack->bound + k);
  fputc(')', trace_file);
}


/*
 * More information about bound k:
 * - print axiom, asserted, derived
 */
static void trace_simplex_bound_origin(int32_t k) {
  simplex_solver_t *solver;
  arith_bstack_t *bstack;

  solver = (simplex_solver_t *) arith_solver;
  bstack = &solver->bstack;
  
  switch (arith_tag_get_expl(bstack->tag[k])) {
  case AEXPL_AXIOM:
    fputs("axiom", trace_file);
    break;
  case AEXPL_ASSERTION:
    fputs("asserted", trace_file);
    break;
  case AEXPL_DERIVED:
    fputs("derived", trace_file);
    break;
  case AEXPL_EGRAPHEQ:
    fputs("egraph equality", trace_file);
    break;
  }
}


/*
 * Print lower/upper bounds on variable x
 */
void trace_simplex_variable_bounds(thvar_t x) {
  simplex_solver_t *solver;
  int32_t k;

  solver = (simplex_solver_t *) arith_solver;
  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0) {
    fprintf(trace_file, "   bound[%"PRId32"]: ", k);
    trace_simplex_bound(k);
    fputc('\n', trace_file);
  }
  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0) {
    fprintf(trace_file, "   bound[%"PRId32"]: ", k);
    trace_simplex_bound(k);
    fputc('\n', trace_file);
  }
}


/*
 * Print the atom attached to literal l
 */
static void trace_atom(literal_t l) {
  bvar_t x;
  void *atom;

  if (is_neg(l)) {
    fputs("(not ", trace_file);
  }
  x = var_of(l);

  if (bvar_has_atom(core, x)) {
    atom = bvar_atom(core, x);

    if (egraph_exists) {
      switch (atom_tag(atom)) {
      case EGRAPH_ATM_TAG:
	trace_egraph_atom(untag_atom(atom));
	break;
      case ARITH_ATM_TAG:
	trace_simplex_atom(untag_atom(atom));
	break;
      case BV_ATM_TAG:
	trace_bv_atom(untag_atom(atom));
	break;
      }
      
    } else {
      switch (arith_type) {
      case NO_SOLVER:
	trace_bv_atom(untag_atom(atom));
	break;

      case SPLX_SOLVER:
	trace_simplex_atom(untag_atom(atom));
	break;

      case IFW_SOLVER:
	trace_idl_atom(untag_atom(atom));
	break;

      case RFW_SOLVER:
	trace_rdl_atom(untag_atom(atom));
	break;
      }      
    }

  } else {
    print_literal(trace_file, l);    
  }

  if (is_neg(l)) {
    fputc(')', trace_file);
  }
}



/*
 * Print a conflict clause: core function
 * - a must be a null-terminated array of literals
 */
static void trace_theory_conflict_core(literal_t *a) {
  literal_t l;

  l = *a;
  if (l >= 0) {
    fprintf(trace_file, "Conflict: (OR ");
    trace_atom(l);
    for (;;) {
      a ++;
      l = *a;
      if (l < 0) break;
      fprintf(trace_file, " ");
      trace_atom(l);
    }
    fprintf(trace_file, ")");
  } else {
    fprintf(trace_file, "Conflict: ()");
  }
  fprintf(trace_file, "\n---\n");
  fflush(trace_file);
}


/*
 * Print a conflict clause:
 * - a must be an array of literals, terminated by null_literal
 */
void trace_theory_conflict(literal_t *a) {
  if (! tracer_ready) return;
  if (! shown_simplex) trace_simplex_tableau();
  trace_theory_conflict_core(a);
}


/*
 * Print a lemma
 * - a must be an array of n literals
 */
void trace_theory_lemma(uint32_t n, literal_t *a) {
  uint32_t i;

  if (! tracer_ready) return;
  if (! shown_simplex) trace_simplex_tableau();

  fprintf(trace_file, "Lemma:      (OR");
  for (i=0; i<n; i++) {
    fputc(' ', trace_file);
    trace_atom(a[i]);
  }
  fprintf(trace_file, ")\n");
  fflush(trace_file);
}


/*
 * Print a theory implication
 * - a = antecedent = array of n literals
 * - l = implied literal
 */
void trace_theory_propagation(uint32_t n, literal_t *a, literal_t l) {
  uint32_t i;

  if (! tracer_ready) return;

  fprintf(trace_file, "Explain prop:\n");
  for (i=0; i<n; i++) {
    fputs("        ", trace_file);
    trace_atom(a[i]);
    fputc('\n', trace_file);
  }
  fputs("implies ", trace_file);
  trace_atom(l);
  fputs("\n---\n", trace_file);
  fflush(trace_file);
}



/*
 * Print a simplex conflict
 */
void trace_simplex_conflict(row_t *row, literal_t *a) {
  if (! tracer_ready) return;

  fprintf(trace_file, "Simplex conflict [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n", 
	  core->decision_level, core->stats.decisions);
  fputs("Row: ", trace_file);
  trace_simplex_row(row);
  fputc('\n', trace_file);
  trace_theory_conflict_core(a);
}


/*
 * Simple conflict; assertion l conflicts with bound k 
 * - a = resulting conflict clause as a null-terminated array of literals
 */
void trace_simplex_assertion_conflict(int32_t k, literal_t l, literal_t *a) {
  if (! tracer_ready) return;

  fprintf(trace_file, "Simplex assertion conflict [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  fputs("Current bound: ", trace_file);
  trace_simplex_bound(k);
  fputs("    ", trace_file);
  trace_simplex_bound_origin(k);
  fputc('\n', trace_file);

  fputs("Assertion: ", trace_file);
  trace_atom(l);
  fputc('\n', trace_file);

  trace_theory_conflict_core(a);
}


/*
 * Print a GCD conflict
 */
void trace_simplex_gcd_conflict(row_t *row, literal_t *a) {
  if (! tracer_ready) return;

  fprintf(trace_file, "GCD conflict [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);
  fputs("Row: ", trace_file);
  trace_simplex_row(row);


  assert(int_hset_is_empty(&hset));
  collect_fixed_vars_of_row(row, &hset);
  int_hset_close(&hset);
  fputs("\nFixed variables\n", trace_file);
  trace_simplex_fixed_variables(&hset);
  fputc('\n', trace_file);
  int_hset_reset(&hset);
  fputs("Reduced row: ", trace_file);
  trace_simplex_reduced_row(row);
  fputc('\n', trace_file);

  trace_theory_conflict_core(a);
}



/*
 * Print a derived bound (x >= b) with antecedent v
 * - v must be a vector of bound indices
 */
void trace_simplex_derived_lb(int32_t x, xrational_t *b, ivector_t *v) {
  simplex_solver_t *solver;
  uint32_t i, n;

  if (! tracer_ready) return;

  solver = (simplex_solver_t *) arith_solver;
  fprintf(trace_file, "Simplex derived bound [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  fputs("Antecedents:\n", trace_file);
  n = v->size;
  for (i=0; i<n; i++) {
    fputs("  ", trace_file);
    trace_simplex_bound(v->data[i]);
    fputc('\n', trace_file);
  }

  fputs("Derived bound:\n", trace_file);
  fputs("  (>= ", trace_file);
  print_simplex_var(trace_file, solver, x);
  fputc(' ', trace_file);
  xq_print(trace_file, b);
  fputs(")\n---\n", trace_file);
  fflush(stdout);
}



/*
 * Print a derived bound (x <= b) with antecedent v
 * - v must be a vector of bound indices
 */
void trace_simplex_derived_ub(int32_t x, xrational_t *b, ivector_t *v) {
  simplex_solver_t *solver;
  uint32_t i, n;

  if (! tracer_ready) return;

  solver = (simplex_solver_t *) arith_solver;
  fprintf(trace_file, "Simplex derived bound [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  fputs("Antecedents:\n", trace_file);
  n = v->size;
  for (i=0; i<n; i++) {
    fputs("  ", trace_file);
    trace_simplex_bound(v->data[i]);
    fputc('\n', trace_file);
  }

  fputs("Derived bound:\n", trace_file);
  fputs("  (<= ", trace_file);
  print_simplex_var(trace_file, solver, x);
  fputc(' ', trace_file);
  xq_print(trace_file, b);
  fputs(")\n---\n", trace_file);
  fflush(stdout);
}



/*
 * Print a conflict between a derived bound (x >= b) and an existing bound k
 * - v = antecedents for the derived bound = vector of bound indices
 * - a = resulting conflict as a null-terminated array of literals
 */
void trace_simplex_derived_lb_conflict(int32_t k, int32_t x, xrational_t *b, ivector_t *v, literal_t *a) {
  simplex_solver_t *solver;
  uint32_t i, n;

  if (! tracer_ready) return;

  solver = (simplex_solver_t *) arith_solver;
  fprintf(trace_file, "Simplex conflict via derived bound [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  fputs("Antecedents:\n", trace_file);
  n = v->size;
  for (i=0; i<n; i++) {
    fputs("  ", trace_file);
    trace_simplex_bound(v->data[i]);
    fputc('\n', trace_file);
  }

  fputs("Derived bound:\n", trace_file);
  fputs("  (>= ", trace_file);
  print_simplex_var(trace_file, solver, x);
  fputc(' ', trace_file);
  xq_print(trace_file, b);
  fputs(")\n", trace_file);

  fputs("Current bound: ", trace_file);
  trace_simplex_bound(k);
  fputs("    ", trace_file);
  trace_simplex_bound_origin(k);
  fputc('\n', trace_file);

  trace_theory_conflict_core(a);
}


/*
 * Print a conflict between a derived bound (x <= b) and an existing bound k
 * - v = antecedents for the derived bound = vector of bound indices
 * - a = resulting conflict as a null-terminated array of literals
 */
void trace_simplex_derived_ub_conflict(int32_t k, int32_t x, xrational_t *b, ivector_t *v, literal_t *a) {
  simplex_solver_t *solver;
  uint32_t i, n;

  if (! tracer_ready) return;

  solver = (simplex_solver_t *) arith_solver;
  fprintf(trace_file, "Simplex conflict via derived bound [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  fputs("Antecedents:\n", trace_file);
  n = v->size;
  for (i=0; i<n; i++) {
    fputs("  ", trace_file);
    trace_simplex_bound(v->data[i]);
    fputc('\n', trace_file);
  }

  fputs("Derived bound:\n", trace_file);
  fputs("  (<= ", trace_file);
  print_simplex_var(trace_file, solver, x);
  fputc(' ', trace_file);
  xq_print(trace_file, b);
  fputs(")\n", trace_file);

  fputs("Current bound: ", trace_file);
  trace_simplex_bound(k);
  fputs("    ", trace_file);
  trace_simplex_bound_origin(k);
  fputc('\n', trace_file);

  trace_theory_conflict_core(a);
}



/*
 * Print a conflict produced by the diophantine solver
 * - v = a set of unsat rows
 * - a = the corresponding conflict (null terminated)
 */
void trace_simplex_dsolver_conflict(ivector_t *v, literal_t *a) {
  simplex_solver_t *solver;
  matrix_t *matrix;
  uint32_t i, n;
  int32_t r;

  if (! tracer_ready) return;

  solver = (simplex_solver_t *) arith_solver;
  matrix = &solver->matrix;

  fprintf(trace_file, "Diophantine conflict [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n", 
	  core->decision_level, core->stats.decisions);

  n = v->size;
  for (i=0; i<n; i++) {
    r = v->data[i];
    fprintf(trace_file, "   row[%"PRId32"]: ", r);  
    trace_simplex_row(matrix->row[r]);
    fputc('\n', trace_file);
  }

  assert(int_hset_is_empty(&hset));
  for (i=0; i<n; i++) {
    r = v->data[i];
    collect_fixed_vars_of_row(matrix->row[r], &hset);
  }
  int_hset_close(&hset);

  if (int_hset_is_nonempty(&hset)) {
    fputs("\nFixed variables\n", trace_file);
    trace_simplex_fixed_variables(&hset);
    int_hset_reset(&hset);
    fputc('\n', trace_file);


    for (i=0; i<n; i++) {
      r = v->data[i];
      fprintf(trace_file, "red. row[%"PRId32"]: ", r);
      trace_simplex_reduced_row(matrix->row[r]);
      fputs("\n", trace_file);
    }
  }

  trace_theory_conflict_core(a);
}


/*
 * Print a conflict produced by egraph propagation
 * - bound k implies (x1 != x2) but the egraph has propagated (x1 == x2)
 * - a = conflict clause as a null-terminated array of literals
 */
void trace_simplex_egraph_eq_conflict(int32_t k, int32_t x1, int32_t x2, literal_t *a) {
  simplex_solver_t *splx;

  if (! tracer_ready) return;

  splx = (simplex_solver_t *) arith_solver;

  fprintf(trace_file, "Simplex/egraph conflict [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  fputs("Bound: ", trace_file);
  trace_simplex_bound(k);
  fputs("    ", trace_file);
  trace_simplex_bound_origin(k);
  fputs("\n  with ", trace_file);
  print_simplex_vardef(trace_file, splx, splx->bstack.var[k]);
  fputs("\n", trace_file);

  fputs("Egraph progated equality: (= ", trace_file);
  print_simplex_var(trace_file, splx, x1);
  fputc(' ', trace_file);
  print_simplex_var(trace_file, splx, x2);
  fputs(")\n\n", trace_file);

  trace_theory_conflict_core(a);
}


/*
 * Print the period and phase for variable x (as implied by x's general solution 
 * found by the diophantine system solver)
 */
void trace_dsolver_var_phase_and_period(int32_t x, rational_t *period, rational_t *phase) {
  simplex_solver_t *solver;
  dsolver_t *dsolver;
  matrix_t *matrix;
  ivector_t *v;
  uint32_t i, n;
  int32_t r;

  if (! tracer_ready) return;

  solver = (simplex_solver_t *) arith_solver;
  matrix = &solver->matrix;
  dsolver = solver->dsolver;
  assert(dsolver != NULL);

  fprintf(trace_file, "Diophantine strengthening [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  v = &buffer;
  assert(v->size == 0);
  dsolver_explain_solution(dsolver, x, v);

  fputs("Rows:\n", trace_file);
  n = v->size;
  for (i=0; i<n; i++) {
    r = v->data[i];
    fprintf(trace_file, "   row[%"PRId32"]: ", r);  
    trace_simplex_row(matrix->row[r]);
    fputc('\n', trace_file);
  }

  assert(int_hset_is_empty(&hset));
  for (i=0; i<n; i++) {
    r = v->data[i];
    collect_fixed_vars_of_row(matrix->row[r], &hset);
  }
  int_hset_close(&hset);

  if (int_hset_is_nonempty(&hset)) {
    fputs("\nFixed variables\n", trace_file);
    trace_simplex_fixed_variables(&hset);
    int_hset_reset(&hset);
    fputc('\n', trace_file);


    for (i=0; i<n; i++) {
      r = v->data[i];
      fprintf(trace_file, "red. row[%"PRId32"]: ", r);
      trace_simplex_reduced_row(matrix->row[r]);
      fputs("\n", trace_file);
    }
  }

  fputs("\nConsequence:\n", trace_file);
  fputs("  (EXISTS (k::int) (= ", trace_file);
  print_simplex_var(trace_file, solver, x);
  if (q_is_nonzero(phase)) {
    fputs(" (+ ", trace_file);
    q_print(trace_file, phase);
    fputs(" (* ", trace_file);
    q_print(trace_file, period);
    fputs(" k))", trace_file);
  } else {
    fputs(" (* ", trace_file);
    q_print(trace_file, period);
    fputs(" k)", trace_file);    
  }
  fputs("))\n---\n", trace_file);
  fflush(trace_file);

  ivector_reset(v);
}






/*
 * Print a derived bound in simplex
 * - row = row from which the bound was derived
 * - k = index of the derived bound in solver->bstack
 */
void trace_simplex_derived_bound(row_t *row, int32_t k) {
  simplex_solver_t *splx;
  int32_t *antecedents;
  int32_t j;
 
  if (! tracer_ready) return;

  splx = (simplex_solver_t *) arith_solver;

  fprintf(trace_file, "Simplex derived bound [dlevel = %"PRId32", decisions = %"PRIu64"]\n\n",
	  core->decision_level, core->stats.decisions);

  fputs("Row: ", trace_file);
  trace_simplex_row(row);
  fputc('\n', trace_file);

  // get the antecedent (array of bound indices, terminated by -1)
  antecedents = splx->bstack.expl[k].ptr;

  fputs("\nAntecedents:\n", trace_file);
  j = *antecedents ++;
  while (j >= 0) {
    fputs("  ", trace_file);
    trace_simplex_bound(j);
    fputc('\n', trace_file);
    j = *antecedents ++;
  }

  fputs("\nDerived bound:\n  ", trace_file);
  trace_simplex_bound(k);
  fputc('\n', trace_file);
  trace_simplex_basic_var(row);
  fputs("\n---\n", trace_file);
  fflush(trace_file);
}




/*
 * Print antecedents for a derived bounds
 * - for every monomial (a * y) of row with y != x
 * - print either the lower bound or the upper bound on y, depending on
 *   the sign of a
 */
static void trace_simplex_lower_bounds_as_antecedents(simplex_solver_t *solver, row_t *row, int32_t x) {
  uint32_t i, n;
  int32_t y, k;

  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      /*
       * lower bound on (a * y) = a * lb[y] if a>0 or a * ub[y] if a < 0
       */
      if (q_is_pos(&row->data[i].coeff)) {
	k = arith_var_lower_index(&solver->vtbl, y);
      } else {
	k = arith_var_upper_index(&solver->vtbl, y);
      }
      assert(k >= 0);
      fputs("  ", trace_file);
      trace_simplex_bound(k);
      fputc('\n', trace_file);
    }
  }
}

static void trace_simplex_upper_bounds_as_antecedents(simplex_solver_t *solver, row_t *row, int32_t x) {
  uint32_t i, n;
  int32_t y, k;

  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      /*
       * upper bound on (a * y) = a * ub[y] if a>0 or a * lb[y] if a < 0
       */
      if (q_is_pos(&row->data[i].coeff)) {
	k = arith_var_upper_index(&solver->vtbl, y);
      } else {
	k = arith_var_lower_index(&solver->vtbl, y);
      }
      assert(k >= 0);
      fputs("  ", trace_file);
      trace_simplex_bound(k);
      fputc('\n', trace_file);
    }
  }
}


/*
 * Check whether x has positive coefficient in row
 */
static bool var_has_positive_coeff_in_row(row_t *row, int32_t x) {
  uint32_t i, n;

  n = row->size;
  for (i=0; i<n; i++) {
    if (row->data[i].c_idx == x) {
      return q_is_pos(&row->data[i].coeff);
    }
  }
  return false;
}


/*
 * Derived lower bound on x
 */
void trace_simplex_implied_lb(row_t *row, int32_t x, xrational_t *a) {
  simplex_solver_t *splx;

  if (! tracer_ready) return;

  splx = (simplex_solver_t *) arith_solver;

  fprintf(trace_file, "Simplex derived lb [dlevel = %"PRIu32", decisions = %"PRIu64"]\n",
	  core->decision_level, core->stats.decisions);

  fputs("Row: ", trace_file);
  trace_simplex_row(row);
  fputc('\n', trace_file);

  fputs("Antecedents:\n", trace_file);
  if (var_has_positive_coeff_in_row(row, x)) {
    trace_simplex_upper_bounds_as_antecedents(splx, row, x);
  } else {
    trace_simplex_lower_bounds_as_antecedents(splx, row, x);
  }

  fputs("Implied bound: (>= ", trace_file);
  print_simplex_var(trace_file, splx, x);
  fputc(' ', trace_file);
  xq_print(trace_file, a);
  fputs(")\n---\n", trace_file);
  fflush(trace_file);
  
}


/*
 * Derived upper bound on x
 */
void trace_simplex_implied_ub(row_t *row, int32_t x, xrational_t *a) {
  simplex_solver_t *splx;

  if (! tracer_ready) return;

  splx = (simplex_solver_t *) arith_solver;

  fprintf(trace_file, "Simplex derived ub [dlevel = %"PRIu32", decisions = %"PRIu64"]\n",
	  core->decision_level, core->stats.decisions);

  fputs("Row: ", trace_file);
  trace_simplex_row(row);
  fputc('\n', trace_file);

  fputs("Antecedents:\n", trace_file);
  if (var_has_positive_coeff_in_row(row, x)) {
    trace_simplex_lower_bounds_as_antecedents(splx, row, x);
  } else {
    trace_simplex_upper_bounds_as_antecedents(splx, row, x);
  }

  fputs("Implied bound: (<= ", trace_file);
  print_simplex_var(trace_file, splx, x);
  fputc(' ', trace_file);
  xq_print(trace_file, a);
  fputs(")\n---\n", trace_file);
  fflush(trace_file);
  
}



/*
 * Print the implication: bound k ==> literal l
 */
void trace_simplex_implied_literal(int32_t k, literal_t l) {
  if (! tracer_ready) return;

  fprintf(trace_file, "Simplex implied literal [dlevel = %"PRIu32", decisions = %"PRIu64"]\n", 
	  core->decision_level, core->stats.decisions);
  
  fputs("Bound: ", trace_file);
  trace_simplex_bound(k);
  fputs("    ", trace_file);
  trace_simplex_bound_origin(k);
  fputs("\nImplied atom: ", trace_file);
  trace_atom(l);
  fputs("\n---\n", trace_file);
  fflush(trace_file);
}




/*
 * Print a simplex assertion (index + sign)
 */
static void trace_simplex_assertion(int32_t a) {
  simplex_solver_t *splx;
  arith_atom_t *atom;
  int32_t i;

  splx = (simplex_solver_t *) arith_solver;

  i = a>>1; // atom index for a
  atom = arith_atom(&splx->atbl, i);
  trace_atom(mk_lit(boolvar_of_atom(atom), ((uint32_t) a) & 1));  
}


/*
 * Multiple implications from a single derived bound
 * - row + v = antecedents for the derived bound
 * - w = assertions implied by the derived bounds
 */
void trace_simplex_multiprops(row_t *row, ivector_t *v, ivector_t *w) {
  uint32_t i, n;

  if (! tracer_ready) return;

  fprintf(trace_file, "Simplex multiple props [dlevel = %"PRIu32", decisions = %"PRIu64"]\n", 
	  core->decision_level, core->stats.decisions);
  fputs("        ", trace_file);
  trace_simplex_row(row);
  fputc('\n', trace_file);
  
  // v = antecedent array = array of bound indices 
  n = v->size;
  for (i=0; i<n; i++) {
    fputs("        ", trace_file);
    trace_simplex_bound(v->data[i]);
    fputc('\n', trace_file);
  }

  fputs("implied literals\n", trace_file);
  n = w->size;
  for (i=0; i<n; i++) {
    fputs("        ", trace_file);
    trace_simplex_assertion(w->data[i]);
    fputc('\n', trace_file);    
  }
  fputs("---\n", trace_file);
  fflush(trace_file);
}



/*
 * Print the tableau and all bounds
 * - similar to trace_simplex_tableau, but uses a different format
 */
void trace_tableau(void) {
  simplex_solver_t *splx;
  matrix_t *matrix;
  row_t *row;
  arith_bstack_t *bstack;
  uint32_t i, n;

  if (! tracer_ready) return;

  fprintf(trace_file, "Simplex tableau [dlevel = %"PRIu32", decisions = %"PRIu64"]\n",
	  core->decision_level, core->stats.decisions);

  splx = (simplex_solver_t *) arith_solver;
  matrix = &splx->matrix;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix_row(matrix, i);
    trace_simplex_row(row);
    fputc('\n', trace_file);
  }

  fputs("\nBounds:\n", trace_file);
  bstack = &splx->bstack;
  n = bstack->top;
  for (i=0; i<n; i++) {
    fputs("  ", trace_file);
    trace_simplex_bound(i);
    fputs("     ", trace_file);
    trace_simplex_bound_origin(i);
    fputc('\n', trace_file);
  }

  fputs("---\n\n", trace_file);
  fflush(trace_file);
}
