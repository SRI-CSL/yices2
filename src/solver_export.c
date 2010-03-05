/*
 * Print a solver state in Yices 1 format.
 */

#include <assert.h>
#include <inttypes.h>

#include "solver_export.h"



/*
 * SIMPLEX TERMS AND VARIABLES
 */

/*
 * Print a simplex variable
 *  "i_<nn>" for an integer variable
 *  "z_<nn>" for a real variable
 */
static void export_avar(FILE *f, arith_vartable_t *table, thvar_t v) {
  if (arith_var_is_int(table, v)) {
    fprintf(f, "i_%"PRId32, v);
  } else {
    fprintf(f, "z_%"PRId32, v);
  }
}


/*
 * Print a monomial
 */ 
static void export_avar_monomial(FILE *f, arith_vartable_t *table, thvar_t v, rational_t *coeff) {
  if (v == const_idx) {
    q_print(f, coeff);
  } else if (q_is_one(coeff)) {
    export_avar(f, table, v);
  } else {
    fputs("(* ", f);
    q_print(f, coeff);
    fputc(' ', f);
    export_avar(f, table, v);
    fputc(')', f);
  }
}


/*
 * Linear polynomial
 */
static void export_avar_poly(FILE *f, arith_vartable_t *table, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else if (n == 1) {
    export_avar_monomial(f, table, p->mono[0].var, &p->mono[0].coeff);
  } else {
    fputs("(+", f);
    for (i=0; i<n; i++) {
      fputc(' ', f);
      export_avar_monomial(f, table, p->mono[i].var, &p->mono[i].coeff);
    }
    fputc(')', f);
  }
}


/*
 * Print a product of variables
 */
static void export_avar_product(FILE *f, arith_vartable_t *table, varprod_t *p) {
  uint32_t i, n, m;
  int32_t x;
  
  n = p->len;
  if (n == 0) {
    fputc('1', f);
  } else if (n == 1 && p->prod[0].exp == 1) {
    export_avar(f, table, p->prod[0].var);
  } else {
    fputs("(*", f);
    for (i=0; i<n; i++) {
      x = p->prod[i].var;
      m = p->prod[i].exp;
      while (m > 0) {
	fputc(' ', f);
	export_avar(f, table, x);
	m --;
      }
    }
    fputc(')', f);
  }
}



/*
 * Print declaration of all variables in table (and their definition if any)
 */
static void export_arith_vartable(FILE *f, arith_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=0; i<n; i++) {
    fputs("(define ", f);
    export_avar(f, table, i);
    if (arith_var_is_int(table, i)) {
      fputs("::int", f);
    } else {
      fputs("::real", f);
    }
    if (arith_var_def_is_poly(table, i)) {
      fputc(' ', f);
      export_avar_poly(f, table, arith_var_poly_def(table, i));
    } else if (arith_var_def_is_product(table, i)) {
      fputc(' ', f);
      export_avar_product(f, table, arith_var_product_def(table, i));
    }
    fputs(")\n", f);
  }
  fputc('\n', f);
}




/*
 * SIMPLEX MATRIX
 */

/*
 * A row is printed as (assert (= .... 0))
 */
static void export_row(FILE *f, arith_vartable_t *vtbl, row_t *row) {
  uint32_t i, n;
  int32_t x;

  fputs("(assert (=", f);
  if (row->nelems == 0) {
    fputs(" 0", f);
  } else {
    if (row->nelems > 1) {
      fputs(" (+", f);
    }
    n = row->size;
    for (i=0; i<n; i++) {
      x = row->data[i].c_idx;
      if (x >= 0) {
	fputc(' ', f);
	export_avar_monomial(f, vtbl, x, &row->data[i].coeff);
      }
    }
    if (row->nelems > 1) {
      fputc(')', f);
    }
  }
  fputs(" 0))\n", f);
}


/*
 * Full constraint matrix
 */
static void export_matrix(FILE *f, arith_vartable_t *vtbl, matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    export_row(f, vtbl, matrix->row[i]);
  }
  fputc('\n', f);
}



/*
 * All bounds asserted at level 0 in bstack
 */
static void export_avar_bounds(FILE *f, arith_vartable_t *vtbl, arith_bstack_t *bstack) {
  uint32_t i, n;
  xrational_t *b;
  int32_t x;

  n = bstack->top;
  for (i=0; i<n; i++) {
    if (arith_tag_get_expl(bstack->tag[i]) == AEXPL_AXIOM) {
      // that's a top-level bound
      fputs("(assert (", f);
      b = bstack->bound + i;
      x = bstack->var[i];

      // find the comparison type
      if (arith_tag_get_type(bstack->tag[i]) == ATYPE_UB) {
	// upper bound: (x <= b)
	if (xq_is_rational(b)) {
	  fputs("<=", f);
	} else {
	  // (x <= b - delta) encodes (x < b)
	  assert(q_is_minus_one(&b->delta));
	  fputc('<', f);
	}
      } else {
	// lower bound: (x >= n)
	if (xq_is_rational(b)) {
	  fputs(">=", f);
	} else {
	  assert(q_is_one(&b->delta));
	  fputc('>', f);
	}
      }
      
      fputc(' ', f);
      export_avar(f, vtbl, x);
      fputc(' ', f);
      q_print(f, &b->main);
      fputs("))\n", f);
    }
  }
  fputc('\n', f);
}



/*
 * All arithmetic constraints in simplex solver
 */
static void export_simplex_constraints(FILE *f, simplex_solver_t *solver) {
  export_matrix(f, &solver->vtbl, &solver->matrix);
  export_avar_bounds(f, &solver->vtbl, &solver->bstack);
}





/*
 * BOOLEANS
 */
static void export_bvar(FILE *f, bvar_t x) {
  assert(x >= 0);
  if (x == bool_const) {
    fputs("true", f);
  } else {
    fprintf(f, "p_%"PRId32, x);
  }
}

static void export_literal(FILE *f, literal_t l) {
  if (l == true_literal) {
    fputs("true", f);
  } else if (l == false_literal) {
    fputs("false", f);
  } else if (is_neg(l)) {
    fputs("(not ", f);
    export_bvar(f, var_of(l));
    fputc(')', f);
  } else {
    export_bvar(f, var_of(l));
  }
}


/*
 * Clauses are printed in the form (assert (or ...))
 */
static void export_clause(FILE *f, clause_t *cl) {
  uint32_t i;
  literal_t l;

  fputs("(assert (or", f);
  i = 0;
  for (;;) {
    l = cl->cl[i];
    if (l < 0) break;
    fputc(' ', f);
    export_literal(f, l);
    i ++;
  }
  fputs("))\n", f);
}

static void export_unit_clause(FILE *f, literal_t l) {
  fputs("(assert ", f);
  export_literal(f, l);
  fputs(")\n", f);
}

static void export_binary_clause(FILE *f, literal_t l1, literal_t l2) {
  fputs("(assert (or ", f);
  export_literal(f, l1);
  fputc(' ', f);
  export_literal(f, l2);
  fputs("))\n", f);
}


/*
 * All clauses in core
 */
static void export_unit_clauses(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;

  n = core->nb_unit_clauses;
  stack = &core->stack;
  for (i=0; i<n; i++) {
    export_unit_clause(f, stack->lit[i]);
  }
}

static void export_binary_clauses(FILE *f, smt_core_t *core) {
    int32_t n;
  literal_t l1, l2;
  literal_t *bin;

  n = core->nlits;  
  for (l1=0; l1<n; l1++) {
    bin = core->bin[l1];
    if (bin != NULL) {
      for (;;) {
	l2 = *bin++;
	if (l2 < 0) break;
	if (l1 <= l2) {
	  export_binary_clause(f, l1, l2);
	}
      }
    }
  }
}


static void export_clause_vector(FILE *f, clause_t **vector) {
  uint32_t i, n;

  n = get_cv_size(vector);
  for (i=0; i<n; i++) {
    export_clause(f, vector[i]);
  }
}


static inline void export_problem_clauses(FILE *f, smt_core_t *core) {
  export_clause_vector(f, core->problem_clauses);
}

static inline void export_learned_clauses(FILE *f, smt_core_t *core) {
  export_clause_vector(f, core->learned_clauses);
}


/*
 * Export all clauses:
 * - if include_learned, then learned clauses are printed too
 * (NOTE: this does not print the empty clause if it was asserted)
 * so this should not be used if core is unsat
 */
static void export_clauses(FILE *f, smt_core_t *core, bool include_learned) {
  export_unit_clauses(f, core);
  export_binary_clauses(f, core);
  export_problem_clauses(f, core);
  fputc('\n', f);
  if (include_learned) {
    fputs(";; Learned clauses\n", f);
    export_learned_clauses(f, core);
    fputc('\n', f);
  }
}




/*
 * Declare all boolean variables that don't have an atom attached
 */
static void export_bvar_declarations(FILE *f, smt_core_t *core) {
  uint32_t i, n;

  n = num_vars(core);
  // skip variable 0 (true_literal)
  for (i=1; i<n; i++) { 
    if (! bvar_has_atom(core, i)) {
      fputs("(define ", f);
      export_bvar(f, i);
      fputs("::bool)\n", f);
    }
  }
  fputc('\n', f);
}






/*
 * SIMPLEX ATOMS
 */
static void export_arith_atom(FILE *f, arith_vartable_t *table, arith_atom_t *atom) {
  switch (tag_of_atom(atom)) {
  case GE_ATM:
    fputs("(>= ", f);
    break;
  case LE_ATM:
    fputs("(<= ", f);
    break;
  case EQ_ATM:
    fputs("(= ", f);
    break;
  default:
    fputs("(??? ", f);
    break;
  }
  export_avar(f, table, var_of_atom(atom));
  fputc(' ', f);
  q_print(f, bound_of_atom(atom));
  fputc(')', f);
}


/*
 * All atom definitions
 * - in the form (define p_<nn>::bool ...)
 */
static void export_arith_atomtable(FILE *f, arith_vartable_t *vtbl, arith_atomtable_t *atbl) {
  uint32_t i, n;
  arith_atom_t *a;

  n = atbl->natoms;
  a = atbl->atoms;
  for (i=0; i<n; i++, a++) {
    fputs("(define ", f);
    export_bvar(f, boolvar_of_atom(a));
    fputs("::bool ", f);
    export_arith_atom(f, vtbl, a);
    fputs(")\n", f);
  }
  fputc('\n', f);
}



/*
 * EXPORT THE FULL SIMPLEX SOLVER + CORE
 */
void export_simplex(FILE *f, simplex_solver_t *solver) {
  export_arith_vartable(f, &solver->vtbl);
  export_bvar_declarations(f, solver->core);
  export_arith_atomtable(f, &solver->vtbl, &solver->atbl);
  export_simplex_constraints(f, solver);
  export_clauses(f, solver->core, false);
}
