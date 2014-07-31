/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BASELINE SIMPLEX PROPAGATOR
 * (This code is included in simplex.c via #include "solvers/simplex/simplex_propagator0.h")
 *
 * NOT COMPATIBLE WITH NEW SIMPLEX MODULE (11/03/2008)
 */

/*
 * The propagator can use solver->propagator as a pointer to any object it needs.
 *
 * The propagator interface consists of the following functions:
 * 1) simplex_init_propagator
 *    called in start search after simplify_matrix but before the tableau is constructed
 *    and checked for feasibility
 * 2) simplex_start_propagator
 *    called in start_search after tableau is constructed, feasible, and all initial bounds
 *    are known
 * 3) simplex_reset_propagator: called in simplex_reset and simplex_reset_tableau
 * 4) simplex_delete_propagator: called in delete_simplex_solver
 * 5) simplex_do_propagation: called in simplex_propagate if tableau is feasible
 * 6) simplex_explain_propagation: called in simplex_expand_explanation
 */



/*
 * COMPILE-TIME OPTIONS
 * - set MARK_DERIVED_ATOMS to 1 to ensure implied atoms are "hidden" (in particular, they are not used
 *   as antecedents in further propagation)
 * - set USE_AFFECTED_ROWS to 1 to try propagation via all rows that contain a variable with a new bound
 */
#define MARK_DERIVED_ATOMS 0
#define USE_AFFECTED_ROWS  1


/*
 * Export the OPTIONS as strings
 */

#if MARK_DERIVED_ATOMS
char *simplex_mark_atoms = "mark_atoms";
#else
char *simplex_mark_atoms = "no mark_atoms";
#endif

#if USE_AFFECTED_ROWS
char *simplex_prop_rows = "use_aff_rows";
#else
char *simplex_prop_rows = "last_conflict";
#endif





#if USE_AFFECTED_ROWS

/*
 * Add all rows that occur in the given column to the "rows_to_process" vector
 * - column must be non-null
 */
static void collect_prop_rows_for_variable(simplex_solver_t *solver, column_t *column) {
  matrix_t *matrix;
  ivector_t *to_process;
  uint32_t i, n;
  int32_t r;

  assert(column != NULL);

  to_process = &solver->rows_to_process;
  matrix = &solver->matrix;

  n = column->size;
  for (i=0; i<n; i++) {
    r = column->data[i].r_idx;
    if (r >= 0 && matrix_row_is_unmarked(matrix, r)) {
      ivector_push(to_process, r);
      matrix_mark_row(matrix, r);
    }
  }
}

#endif


/*
 * Scan all constraints in the bound queue
 * - collect all rows that depend on these constraints
 *   into the row_to_process vector.
 * - bstack->prop_ptr is not modified
 */
static void collect_relevant_prop_rows(simplex_solver_t *solver) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  matrix_t *matrix;
#if USE_AFFECTED_ROWS
  column_t *col;
  uint32_t i;
  thvar_t x;
#endif
  int32_t r;

  bstack = &solver->bstack;
  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  assert(solver->rows_to_process.size == 0);

  r = solver->last_conflict_row;
  if (r >= 0 && matrix_row_is_unmarked(matrix, r)) {
    ivector_push(&solver->rows_to_process, r);
    matrix_mark_row(matrix, r);
  }

#if USE_AFFECTED_ROWS
  for (i = bstack->prop_ptr; i<bstack->top; i++) {
    x = bstack->var[i];
    col = matrix->column[x];
    if (col != NULL) {
      // skip the bound if it's not the current upper/lower bound on x
      if (arith_var_lower_index(vtbl, x) == i || arith_var_upper_index(vtbl, x) == i) {
        collect_prop_rows_for_variable(solver, col);
      }
    }
  }
#endif

}


/*
 * Check whether x has unassigned atoms
 */
static bool var_has_unassigned_atoms(simplex_solver_t *solver, thvar_t x) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  uint32_t i, n;

  atbl = &solver->atbl;
  atom_vector = arith_var_atom_vector(&solver->vtbl, x);
  if (atom_vector != NULL) {
    n = iv_size(atom_vector);
    for (i=0; i<n; i++) {
      if (arith_atom_is_unmarked(atbl, atom_vector[i])) {
        return true;
      }
    }
  }
  return false;
}



/*
 * Conversion from assertion index to literal
 */
static literal_t literal_of_assertion(simplex_solver_t *solver, int32_t a) {
  arith_atom_t *atom;
  int32_t i;

  i = atom_of_assertion(a);
  atom = arith_atom(&solver->atbl, i);
  return mk_lit(boolvar_of_atom(atom), sign_of_assertion(a));
}




/*
 * Explain the upper bounds on all monomials of p
 * - skip the monomial that contains variable x
 * - the explanations are bound indices stored in vector v
 * - explanation for a.y <= c is the current upper index on y if a>0
 *                            or the current lower index of y if a<0
 */
static void explain_upper_bounds(simplex_solver_t *solver, thvar_t x, row_t *p, ivector_t *v) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  int32_t k;
  thvar_t y;

  vtbl = &solver->vtbl;
  n = p->size;
  for (i=0; i<n; i++) {
    y = p->data[i].c_idx;
    if (y >= 0 && y != x) {
      // explain bound: a.y <= c
      if (q_is_pos(&p->data[i].coeff)) {
        k = arith_var_upper_index(vtbl, y);
      } else {
        k = arith_var_lower_index(vtbl, y);
      }
      assert(k >= 0);
      ivector_push(v, k);
    }
  }
}


/*
 * Explain the lower bounds on all monomials of p
 * - skip the monomial that contains variable x
 * - the explanation indices are stored in vector v
 * - explanation for a.y >= c is the current lower index of y if a>0
 *                or the current upper index of y if a<0
 */
static void explain_lower_bounds(simplex_solver_t *solver, thvar_t x, row_t *p, ivector_t *v) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  int32_t k;
  thvar_t y;

  vtbl = &solver->vtbl;
  n = p->size;
  for (i=0; i<n; i++) {
    y = p->data[i].c_idx;
    if (y >= 0 && y != x) {
      // explain bound: a.y <= c
      if (q_is_pos(&p->data[i].coeff)) {
        k = arith_var_lower_index(vtbl, y);
      } else {
        k = arith_var_upper_index(vtbl, y);
      }
      assert(k >= 0);
      ivector_push(v, k);
    }
  }
}


/*
 * Convert vector v of bound indices to a vector of literals
 * - if bound k is in v and is has a non-null explanation l, then k is replaced by l
 * - if bound k is in v and has a null explanation it's removed (k is an axiom)
 */
static void convert_bounds_to_literals(simplex_solver_t *solver, ivector_t *v) {
  uint32_t i, j, n;
  int32_t k;
  literal_t l;

  n = v->size;
  j = 0;
  for (i=0; i<n; i++) {
    k = v->data[i];
    assert(0 <= k && k < solver->bstack.top);
    l = solver->bstack.expl[k];
    if (l != null_literal) {
      assert(literal_value(solver->core, l) == VAL_TRUE);
      v->data[j] = l;
      j ++;
    }
  }
  ivector_shrink(v, j);
}


/*
 * Check whether b is larger than the current lower bound on x
 * - x = variable
 * - b = computed lower bound
 */
static bool useful_lower_bound(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_bstack_t *bstack;
  int32_t k;

  bstack = &solver->bstack;
  k = arith_var_lower_index(&solver->vtbl, x);
  if (k < 0 || xq_lt(bstack->bound + k, b)) {
    // the derived bound is not redundant
#if TRACE_PROPAGATION
    printf("     new bound\n");
#endif
    return true;
  } else {
#if TRACE_PROPAGATION
    printf("     redundant\n");
#endif
    return false;
  }
}


/*
 * Check whether b is larger than the current upper bound on x
 * If so find an unassigned atom that's implied by (x <= b)
 * - x = variable
 * - b = computed lower bound
 */
static bool useful_upper_bound(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_bstack_t *bstack;
  int32_t k;

  bstack = &solver->bstack;
  k = arith_var_upper_index(&solver->vtbl, x);
  if (k < 0 || xq_gt(bstack->bound + k, b)) {
    // the derived bound is not redundant
#if TRACE_PROPAGATION
    printf("     new bound\n");
#endif
    return true;
  } else {
#if TRACE_PROPAGATION
    printf("     redundant\n");
#endif
    return false;
  }
}





/*
 * FIRST VARIANT: ONLY ONE ATOM PROPAGATED FOR EACH DERIVED BOUNDS
 */

/*
 * Find the strongest atom implied by (x >= b)
 * - the result is a 32bit integer encoding an atom id + a polarity sign
 *   this encodes either (x >= c) with b>=c (sign = 0)
 *               or (not (x <= c)) with b>c (sign = 1)
 * - return -1 if there's no implied atom
 * - x must have a non-null atom vector
 */
static int32_t assertion_implied_by_lb(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom;
  rational_t *best, *c;
  uint32_t i, n;
  int32_t k, cmp, a;

  atbl = &solver->atbl;
  atom_vector = arith_var_atom_vector(&solver->vtbl, x);
  assert(atom_vector != NULL);

  a = -1;
  best = NULL;
  n = iv_size(atom_vector);
  for (i=0; i<n; i++) {
    k = atom_vector[i];
    if (arith_atom_is_unmarked(atbl, k)) {
      atom = arith_atom(atbl, k);
      assert(var_of_atom(atom) == x);
      c = bound_of_atom(atom);
      cmp = xq_cmp_q(b, c);
      /*
       * cmp < 0 means b < c
       * cmp = 0 means b = c
       * cmp > 0 means b > c
       */
      if (atom_is_ge(atom)) {
        if (cmp >= 0) {
          // implied atom: (x >= c) with (b >= c)
          if (a < 0 || q_lt(c, best)) {
            a = mk_true_assertion(k);
            best = c;
          }
          if (cmp == 0) break; //b == c: can't improve
        }
      } else {
        assert(atom_is_le(atom));
        if (cmp > 0) {
          // implied atom: (not (x <= c)) with (b>c)
          if (a < 0 || q_le(c, best)) {
            a = mk_false_assertion(k);
            best = c;
          }
        }
      }
    }
  }

  return a;
}


/*
 * Find the strongest atom implied by (x <= b)
 * - the result is a 32bit integer encoding an atom id + a polarity sign
 *   this encodes either (x <= c) with b<=c (sign = 0)
 *               or (not (x >= c)) with b<c (sign = 1)
 * - return -1 if there's no implied atom
 * - x must have a non-null atom vector
 */
static int32_t assertion_implied_by_ub(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom;
  rational_t *best, *c;
  uint32_t i, n;
  int32_t k, cmp, a;

  atbl = &solver->atbl;
  atom_vector = arith_var_atom_vector(&solver->vtbl, x);
  assert(atom_vector != NULL);

  a = -1;
  best = NULL;
  n = iv_size(atom_vector);
  for (i=0; i<n; i++) {
    k = atom_vector[i];
    if (arith_atom_is_unmarked(atbl, k)) {
      atom = arith_atom(atbl, k);
      assert(var_of_atom(atom) == x);
      c = bound_of_atom(atom);
      cmp = xq_cmp_q(b, c);
      /*
       * cmp < 0 means b < c
       * cmp = 0 means b = c
       * cmp > 0 means b > c
       */
      if (atom_is_ge(atom)) {
        if (cmp < 0) {
          // implied atom: (not (x >= c)) with (b < c)
          if (a < 0 || q_le(c, best)) {
            a = mk_false_assertion(k);
            best = c;
          }
        }
      } else {
        assert(atom_is_le(atom));
        if (cmp <= 0) {
          // implied atom: (x <= c) with (b <= c)
          if (a < 0 || q_lt(c, best)) {
            a = mk_true_assertion(k);
            best = c;
          }
          if (c == 0) break; // can't improve on (x <= b)
        }
      }
    }
  }

  return a;
}





/*
 * Theory propagation: l implied by asserted bounds
 * - v: vector of bound indices that imply l
 *
 * HACK TO FIX A BUG:
 * - there's a chance that the same l gets implied twice (in different rows)
 * - this may happen if MARK_DERIVED_ATOMS is 0 and USE_AFFECTED_ROWS is 1
 * - so we check here whether l is undef before propagating to the core
 */
static void simplex_theory_prop(simplex_solver_t *solver, literal_t l, ivector_t *v) {
  literal_t *expl;
  uint32_t i, n;

  /*
   * Theory propagation from a feasible tableau can't imply both l and not l
   * so l should be either true or undef in the core.
   */
  assert(literal_value(solver->core, l) != VAL_FALSE);

  // build explanation as a conjunction of literals in v
  convert_bounds_to_literals(solver, v);
  n = v->size;
  if (n < solver->small_prop_threshold) {
    // create a lemma: turn (v ==> l) into a clause
    solver->stats.num_prop_lemmas ++;
    convert_expl_to_clause(v);
    ivector_push(v, l);
    add_clause(solver->core, v->size, v->data); // v may be modified but that's OK
  } else if (literal_value(solver->core, l) == VAL_UNDEF) {
    // copy the explanation in the arena (and add an end-marker)
    solver->stats.num_props ++;
    expl = (literal_t *) arena_alloc(&solver->arena, (n+1) * sizeof(literal_t));
    for (i=0; i<n; i++) {
      expl[i] = v->data[i];
    }
    expl[i] = null_literal;
    propagate_literal(solver->core, l, expl);

#if TRACE_PROPAGATION
  } else {
    printf("--> skipping twice implied literal: ");
    print_literal(stdout, l);
    printf("\n     ");
    print_simplex_atomdef(stdout, solver, var_of(l));
#endif
  }
}


/*
 * Theory propagation: assertion implied by the upper bounds on monomials of row p
 * - a = assertion index = atom id + sign bit
 * - x = variable of a (to skip in explanations)
 * - p = row
 */
static void theory_prop_from_upper_bounds(simplex_solver_t *solver, int32_t a, thvar_t x, row_t *p) {
  ivector_t *v;
  literal_t l;

  v = &solver->aux_vector;
  l = literal_of_assertion(solver, a);
  assert(v->size == 0);
  explain_upper_bounds(solver, x, p, v);

#if TRACE_THEORY
  trace_simplex_implied_literal(p, v, l);
#endif

  simplex_theory_prop(solver, l, v);

#if MARK_DERIVED_ATOMS
  // mark the atm and add it to the assertion queue (for backtracking)
  push_assertion(&solver->assertion_queue, a);
  mark_arith_atom(&solver->atbl, atom_of_assertion(a));
#endif

#if TRACE_PROPAGATION
  printf("     implied literal: ");
  print_literal(stdout, l);
  printf("\n     ");
  print_simplex_atomdef(stdout, solver, var_of(l));
#endif

  ivector_reset(v);
}


/*
 * Theory propagation: assertion implied by the lower bounds on monomials of row p
 * - a = assertion index = atom id + sign bit
 * - x = variable of a (to skip in explanations)
 * - p = row
 */
static void theory_prop_from_lower_bounds(simplex_solver_t *solver, int32_t a, thvar_t x, row_t *p) {
  ivector_t *v;
  literal_t l;

  v = &solver->aux_vector;
  l = literal_of_assertion(solver, a);
  assert(v->size == 0);
  explain_lower_bounds(solver, x, p, v);

#if TRACE_THEORY
  trace_simplex_implied_literal(p, v, l);
#endif

  simplex_theory_prop(solver, l, v);

#if MARK_DERIVED_ATOMS
  push_assertion(&solver->assertion_queue, a);
  mark_arith_atom(&solver->atbl, atom_of_assertion(a));
#endif

#if TRACE_PROPAGATION
  printf("     implied literal: ");
  print_literal(stdout, l);
  printf("\n     ");
  print_simplex_atomdef(stdout, solver, var_of(l));
#endif

  ivector_reset(v);
}




/*
 * SECOND VARIANT: PROPAGATE ALL ATOMS IMPLIED BY A DERIVED BOUNDS
 */

/*
 * Collect all the unassigned atoms implied by (x >= b) into vector v
 * - each element of v is a 32bit assertion code: atom id + polarity sign
 * - assertion code with sign = 0 is for an atom (x >= c) with b >= c
 *   assertion code with sign = 1 is for an atom (not (x <= c)) with b > c
 * - x must have a non-null atom vector
 */
static void all_assertions_implied_by_lb(simplex_solver_t *solver, thvar_t x, xrational_t *b, ivector_t *v) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom;
  uint32_t i, n;
  int32_t k;

  atbl = &solver->atbl;
  atom_vector = arith_var_atom_vector(&solver->vtbl, x);
  assert(atom_vector != NULL);

  n = iv_size(atom_vector);
  for (i=0; i<n; i++) {
    k = atom_vector[i];
    if (arith_atom_is_unmarked(atbl, k)) {
      // atom k is not assigned
      atom = arith_atom(atbl, k);
      assert(var_of_atom(atom) == x);
      if (atom_is_ge(atom)) {
        // atom is (x >= c) where c = bound_of_atom(atom)
        if (xq_ge_q(b, bound_of_atom(atom))) {
          // b >= c so k is implied by (x >= b)
          ivector_push(v, mk_true_assertion(k));
        }
      } else {
        assert(atom_is_le(atom));
        // atom is (x <= c) where c = bound_of_atom(atom)
        if (xq_gt_q(b, bound_of_atom(atom))) {
          // b > c so (not k) (i.e., x > c) is implied by (x >= b)
          ivector_push(v, mk_false_assertion(k));
        }
      }
    }
  }
}



/*
 * Collect all the unassigned atoms implied by (x <= b) into vector v
 * - each element of v is a 32bit assertion code: atom id + polarity sign
 * - assertion code with sign = 0 is for an atom (x <= c) with b <= c
 *   assertion code with sign = 1 is for an atom (not (x >= c)) with b < c
 * - x must have a non-null atom vector
 */
static void all_assertions_implied_by_ub(simplex_solver_t *solver, thvar_t x, xrational_t *b, ivector_t *v) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom;
  uint32_t i, n;
  int32_t k;

  atbl = &solver->atbl;
  atom_vector = arith_var_atom_vector(&solver->vtbl, x);
  assert(atom_vector != NULL);

  n = iv_size(atom_vector);
  for (i=0; i<n; i++) {
    k = atom_vector[i];
    if (arith_atom_is_unmarked(atbl, k)) {
      // atom k is not assigned
      atom = arith_atom(atbl, k);
      assert(var_of_atom(atom) == x);
      if (atom_is_ge(atom)) {
        // atom is (x >= c) where c = bound_of_atom(atom)
        if (xq_lt_q(b, bound_of_atom(atom))) {
          // b < c so (not k) (i.e., x < c) is implied by (x <= b)
          ivector_push(v, mk_false_assertion(k));
        }
      } else {
        assert(atom_is_le(atom));
        // atom is (x <= c) where c = bound_of_atom(atom)
        if (xq_le_q(b, bound_of_atom(atom))) {
          // b <= c so k is implied by (x <= b)
          ivector_push(v, mk_true_assertion(k));
        }
      }
    }
  }
}




/*
 * Multiple propagations with explanations in vector w
 * - w is a vector of literals (interpreted as a conjunction of literals)
 * - all elements of vector v encode assertions implied by w
 * - vector w is modified
 */
static void multiple_theory_props(simplex_solver_t *solver, ivector_t *v, ivector_t *w) {
  literal_t *expl;
  uint32_t i, n, m;
  int32_t k;
  literal_t l;

  m = w->size;
  n = v->size;

  if (m < solver->small_prop_threshold) {
    // Prepare to create lemmas (w ==> l) as clauses
    convert_expl_to_clause(w);
    ivector_push(w, null_literal); // make room for l
    assert(w->size == m + 1);

    for (i=0; i<n; i++) {
      k = v->data[i];
      assert(arith_atom_is_unmarked(&solver->atbl, atom_of_assertion(k)));
      l = literal_of_assertion(solver, k);
      assert(literal_value(solver->core, l) != VAL_FALSE);

      // create the clause (w ==> l)
      w->data[m] = l;
      add_clause(solver->core, w->size, w->data);

#if MARK_DERIVED_ATOMS
      // mark the atom and add it to the assertion queue
      push_assertion(&solver->assertion_queue, k);
      mark_arith_atom(&solver->atbl, atom_of_assertion(k));
#endif
    }

    solver->stats.num_prop_lemmas += n;

  } else {
    // save the explanaton in the arena and add an end marker
    expl = (literal_t *) arena_alloc(&solver->arena, (m+1) * sizeof(literal_t));
    for (i=0; i<m; i++) {
      expl[i] = w->data[i];
    }
    expl[i] = null_literal;

    for (i=0; i<n; i++) {
      k = v->data[i];
      assert(arith_atom_is_unmarked(&solver->atbl, atom_of_assertion(k)));
      l = literal_of_assertion(solver, k);

      // propagate l with expl as antecedent
      // BUG FIX: we check whether l is already applied (via an other row)
      assert(literal_value(solver->core, l) != VAL_FALSE);
      if (literal_value(solver->core, l) == VAL_UNDEF) {
        propagate_literal(solver->core, l, expl);
      }

#if MARK_DERIVED_ATOMS
      // mark the atom and add it to the assertion queue
      push_assertion(&solver->assertion_queue, k);
      mark_arith_atom(&solver->atbl, atom_of_assertion(k));
#endif
    }

    solver->stats.num_props += n;
  }

}


/*
 * Theory propagation: the elements of v encode assertions implied by the upper bounds
 * on monomials of row p. All these assertions are on variable x.
 */
static void all_theory_props_from_upper_bounds(simplex_solver_t *solver, ivector_t *v, thvar_t x, row_t *p) {
  ivector_t *w;

  if (v->size > 0) {
    w = &solver->aux_vector;
    assert(w->size == 0);

    // explain the bounds: store literals in w
    explain_upper_bounds(solver, x, p, w);

#if TRACE_THEORY
    trace_simplex_multiprops(p, w, v);
#endif

    convert_bounds_to_literals(solver, w);

    // do the propagations
    multiple_theory_props(solver, v, w);

    ivector_reset(w);
  }
}



/*
 * Theory propagation: the elements of v encode assertions implied by the upper bounds
 * on monomials of row p. All these assertions are on variable x.
 */
static void all_theory_props_from_lower_bounds(simplex_solver_t *solver, ivector_t *v, thvar_t x, row_t *p) {
  ivector_t *w;

  if (v->size > 0) {
    w = &solver->aux_vector;
    assert(w->size == 0);

    // explain the bounds
    explain_lower_bounds(solver, x, p, w);

#if TRACE_THEORY
    trace_simplex_multiprops(p, w, v);
#endif

    convert_bounds_to_literals(solver, w);

    // do the propagations
    multiple_theory_props(solver, v, w);

    ivector_reset(w);
  }
}




/*
 * PROPAGATION BASED ON A ROW OF THE TABLEAU
 */

/*
 * Compute the bound implied on y by the other variables of p
 * - all monomials must have an upper bound except a.y
 */
static void try_upper_bound_propagation(simplex_solver_t *solver, thvar_t y, row_t *p)  {
  row_elem_t *a;
  xrational_t *bound, *sum;
  rational_t *c; // coefficient of y in p
  arith_vartable_t *vtbl;
  ivector_t *w;
  uint32_t n;
  thvar_t x;
  int32_t k;

#if TRACE_PROPAGATION
  printf("\n---> try_upper_bound_propagation for ");
  print_simplex_var(stdout, solver, y);
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  bound = solver->bstack.bound;
  vtbl = &solver->vtbl;
  sum = &solver->bound;

  // initialize c to avoid GCC warning
  c = NULL;

  xq_clear(sum);
  n = p->size;
  a = p->data;
  do {
    x = a->c_idx;
    if (x == y) {
      c = &a->coeff;
    } else if (x >= 0) {
      // sum := sum - upper_bound on a.x
      if (q_is_pos(&a->coeff)) {
        k = arith_var_upper_index(vtbl, x);
      } else {
        k = arith_var_lower_index(vtbl, x);
      }

#if TRACE_PROPAGATION
      printf("     ");
      print_simplex_bound(stdout, solver, k);
      printf("\n");
#endif
      assert(k >= 0);
      xq_submul(sum, bound + k, &a->coeff);
    }
    a ++;
    n --;
  } while (n > 0);

  // implied bound: c.y >= sum
  assert(q_is_nonzero(c));
  xq_div(sum, c);
  if (q_is_pos(c)) {

#if TRACE_PROPAGATION
    printf("     implied bound: ");
    print_simplex_var(stdout, solver, y);
    printf(" >= ");
    xq_print(stdout, sum);
    printf("\n");
#endif

    if (useful_lower_bound(solver, y, sum)) {
      if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
        w = &solver->aux_vector2;
        assert(w->size == 0);
        all_assertions_implied_by_lb(solver, y, sum, w);
        all_theory_props_from_upper_bounds(solver, w, y, p);
        ivector_reset(w);
      } else {
        k = assertion_implied_by_lb(solver, y, sum);
        if (k >= 0) {
          theory_prop_from_upper_bounds(solver, k, y, p);
        }
      }
    }

  } else {

#if TRACE_PROPAGATION
    printf("     implied bound: ");
    print_simplex_var(stdout, solver, y);
    printf(" <= ");
    xq_print(stdout, sum);
    printf("\n");
#endif

    if (useful_upper_bound(solver, y, sum)) {
      if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
        w = &solver->aux_vector2;
        assert(w->size == 0);
        all_assertions_implied_by_ub(solver, y, sum, w);
        all_theory_props_from_upper_bounds(solver, w, y, p);
        ivector_reset(w);

      } else {
        k = assertion_implied_by_ub(solver, y, sum);
        if (k >= 0) {
          theory_prop_from_upper_bounds(solver, k, y, p);
        }
      }
    }
  }
}


/*
 * Compute the bound implied on y by the other variables of p
 * - all monomials must have an lower bound except a.y
 */
static void try_lower_bound_propagation(simplex_solver_t *solver, thvar_t y, row_t *p) {
  row_elem_t *a;
  xrational_t *bound, *sum;
  rational_t *c; // coefficient of y in p
  arith_vartable_t *vtbl;
  ivector_t *w;
  uint32_t n;
  thvar_t x;
  int32_t k;

#if TRACE_PROPAGATION
  printf("\n---> try_lower_bound_propagation for ");
  print_simplex_var(stdout, solver, y);
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  bound = solver->bstack.bound;
  vtbl = &solver->vtbl;
  sum = &solver->bound;

  // initialize c to avoid GCC warning
  c = NULL;

  xq_clear(sum);
  n = p->size;
  a = p->data;
  do {
    x = a->c_idx;
    if (x == y) {
      c = &a->coeff;
    } else if (x >= 0) {
      // sum := sum - lower_bound on a.x
      if (q_is_pos(&a->coeff)) {
        k = arith_var_lower_index(vtbl, x);
      } else {
        k = arith_var_upper_index(vtbl, x);
      }
#if TRACE_PROPAGATION
      printf("     ");
      print_simplex_bound(stdout, solver, k);
      printf("\n");
#endif
      assert(k >= 0);
      xq_submul(sum, bound + k, &a->coeff);
    }
    a ++;
    n --;
  } while (n > 0);

  // implied bound: c.y <= sum
  assert(q_is_nonzero(c));
  xq_div(sum, c);
  if (q_is_pos(c)) {

#if TRACE_PROPAGATION
    printf("     implied bound: ");
    print_simplex_var(stdout, solver, y);
    printf(" <= ");
    xq_print(stdout, sum);
    printf("\n");
#endif

    if (useful_upper_bound(solver, y, sum)) {
      if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
        w = &solver->aux_vector2;
        assert(w->size == 0);
        all_assertions_implied_by_ub(solver, y, sum, w);
        all_theory_props_from_lower_bounds(solver, w, y, p);
        ivector_reset(w);
      } else {
        k = assertion_implied_by_ub(solver, y, sum);
        if (k >= 0) {
          theory_prop_from_lower_bounds(solver, k, y, p);
        }
      }

    }

  } else {

#if TRACE_PROPAGATION
    printf("     implied bound: ");
    print_simplex_var(stdout, solver, y);
    printf(" >= ");
    xq_print(stdout, sum);
    printf("\n");
#endif

    if (useful_lower_bound(solver, y, sum)) {
      if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
        w = &solver->aux_vector2;
        assert(w->size == 0);
        all_assertions_implied_by_lb(solver, y, sum, w);
        all_theory_props_from_lower_bounds(solver, w, y, p);
        ivector_reset(w);
      } else {
        k = assertion_implied_by_lb(solver, y, sum);
        if (k >= 0) {
          theory_prop_from_lower_bounds(solver, k, y, p);
        }
      }

    }

  }

}



/*
 * Add the upper bounds of all monomials in row p
 * - all monomials must have an upper bound
 * - the result is stored in b
 */
static void add_upper_bounds(simplex_solver_t *solver, row_t *p, xrational_t *b) {
  row_elem_t *a;
  xrational_t *bound;
  arith_vartable_t *vtbl;
  uint32_t n;
  thvar_t x;
  int32_t k;

  bound = solver->bstack.bound;
  vtbl = &solver->vtbl;

  xq_clear(b);
  n = p->size;
  a = p->data;
  do {
    x = a->c_idx;
    if (x >= 0) {
      if (q_is_pos(&a->coeff)) {
        k = arith_var_upper_index(vtbl, x);
      } else {
        k = arith_var_lower_index(vtbl, x);
      }
      assert(k >= 0);

#if TRACE_PROPAGATION
      printf("     ");
      print_simplex_bound(stdout, solver, k);
      printf("\n");
#endif
      xq_addmul(b, bound + k, &a->coeff);
    }
    a ++;
    n --;
  } while (n > 0);
}


/*
 * Add the lower bounds of all monomials in p
 * - all monomials must have an upper bound
 * - the result is stored in b
 */
static void add_lower_bounds(simplex_solver_t *solver, row_t *p, xrational_t *b) {
  row_elem_t *a;
  xrational_t *bound;
  arith_vartable_t *vtbl;
  uint32_t n;
  thvar_t x;
  int32_t k;

  bound = solver->bstack.bound;
  vtbl = &solver->vtbl;

  xq_clear(b);
  n = p->size;
  a = p->data;
  do {
    x = a->c_idx;
    if (x >= 0) {
      if (q_is_pos(&a->coeff)) {
        k = arith_var_lower_index(vtbl, x);
      } else {
        k = arith_var_upper_index(vtbl, x);
      }
      assert(k >= 0);

#if TRACE_PROPAGATION
      printf("     ");
      print_simplex_bound(stdout, solver, k);
      printf("\n");
#endif
      xq_addmul(b, bound + k, &a->coeff);
    }
    a ++;
    n --;
  } while (n > 0);
}


/*
 * Try propagation for row p when all monomials have an upper bound
 */
static void full_upper_bound_propagation(simplex_solver_t *solver, row_t *p) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  xrational_t *sum, *aux;
  row_elem_t *a;
  ivector_t *w;
  uint32_t n;
  thvar_t x;
  int32_t k;

#if TRACE_PROPAGATION
  printf("\n---> full_upper_bound_propagation");
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  sum = &solver->bound;
  add_upper_bounds(solver, p, sum);
  xq_neg(sum);

  aux = &solver->delta;

  bstack = &solver->bstack;
  vtbl = &solver->vtbl;
  n = p->size;
  a = p->data;
  do {
    /*
     * The row is  a.x + a_1 x_1 + ... + a_n x_n == 0,
     * bounds are  a.x <= u, a_1 x_1 <= u_1, ..., a_n x_n <= u_n,
     * and sum is - (u + u_1 + ... + u_n).
     * - implied bound on a x: a.x >= - (u_1 + ... + u_n) = sum + u
     * - if a>0, then u = a.(upper_bound on x),
     *   implied bound on x: x >= sum/a + u/a = sum/a + (upper_bound on x)
     * - if a<0, then u = a.(lower_bound on x),
     *   implied bound on x: x <= sum/a + u/a = sum/a + (lower_bound on x)
     */
    x = a->c_idx;
    if (x >= 0 && var_has_unassigned_atoms(solver, x)) {
      xq_set(aux, sum);
      xq_div(aux, &a->coeff);
      if (q_is_pos(&a->coeff)) {
        k = arith_var_upper_index(vtbl, x);
        assert(k >= 0);
        xq_add(aux, bstack->bound + k);

#if TRACE_PROPAGATION
        printf("     implied bound: ");
        print_simplex_var(stdout, solver, x);
        printf(" >= ");
        xq_print(stdout, aux);
        printf("\n");
#endif

        if (useful_lower_bound(solver, x, aux)) {
          if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
            w = &solver->aux_vector2;
            assert(w->size == 0);
            all_assertions_implied_by_lb(solver, x, aux, w);
            all_theory_props_from_upper_bounds(solver, w, x, p);
            ivector_reset(w);
          } else {
            k = assertion_implied_by_lb(solver, x, aux);
            if (k >= 0) {
              theory_prop_from_upper_bounds(solver, k, x, p);
            }
          }

        }

      } else {
        k = arith_var_lower_index(vtbl, x);
        assert(k >= 0);
        xq_add(aux, bstack->bound + k);

#if TRACE_PROPAGATION
        printf("     implied bound: ");
        print_simplex_var(stdout, solver, x);
        printf(" <= ");
        xq_print(stdout, aux);
        printf("\n");
#endif

        if (useful_upper_bound(solver, x, aux)) {
          if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
            w = &solver->aux_vector2;
            assert(w->size == 0);
            all_assertions_implied_by_ub(solver, x, aux, w);
            all_theory_props_from_upper_bounds(solver, w, x, p);
            ivector_reset(w);
          } else {
            k = assertion_implied_by_ub(solver, x, aux);
            if (k >= 0) {
              theory_prop_from_upper_bounds(solver, k, x, p);
            }
          }
        }
      }


    }
    a ++;
    n --;
  } while (n > 0);

#if TRACE_PROPAGATION
  printf("\n");
#endif

}


/*
 * Try propagation for row p when all monomials have a lower bound
 */
static void full_lower_bound_propagation(simplex_solver_t *solver, row_t *p) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  xrational_t *sum, *aux;
  row_elem_t *a;
  ivector_t *w;
  uint32_t n;
  thvar_t x;
  int32_t k;

#if TRACE_PROPAGATION
  printf("\n---> full_lower_bound_propagation");
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  sum = &solver->bound;
  add_lower_bounds(solver, p, sum);
  xq_neg(sum);

  aux = &solver->delta;

  bstack = &solver->bstack;
  vtbl = &solver->vtbl;
  n = p->size;
  a = p->data;
  do {
    /*
     * The row is  a.x + a_1 x_1 + ... + a_n x_n == 0,
     * bounds are  a.x >= l, a_1 x_1 >= l_1, ..., a_n x_n >= u_n,
     * and sum is - (l + l_1 + ... + l_n).
     * - implied bound on a x: a.x <= - (l_1 + ... + l_n) = sum + l
     * - if a>0, then l = a.(lower_bound on x),
     *   implied bound on x: x <= sum/a + l/a = sum/a + (lower_bound on x)
     * - if a<0, then l = a.(upper_bound on x),
     *   implied bound on x: x >= sum/a + l/a = sum/a + (upper_bound on x)
     */
    x = a->c_idx;
    if (x >= 0 && var_has_unassigned_atoms(solver, x)) {
      xq_set(aux, sum);
      xq_div(aux, &a->coeff);
      if (q_is_pos(&a->coeff)) {
        k = arith_var_lower_index(vtbl, x);
        assert(k >= 0);
        xq_add(aux, bstack->bound + k);

#if TRACE_PROPAGATION
        printf("     implied bound: ");
        print_simplex_var(stdout, solver, x);
        printf(" <= ");
        xq_print(stdout, aux);
        printf("\n");
#endif

        if (useful_upper_bound(solver, x, aux)) {
          if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
            w = &solver->aux_vector2;
            assert(w->size == 0);
            all_assertions_implied_by_ub(solver, x, aux, w);
            all_theory_props_from_lower_bounds(solver, w, x, p);
            ivector_reset(w);
          } else {
            k = assertion_implied_by_ub(solver, x, aux);
            if (k >= 0) {
              theory_prop_from_lower_bounds(solver, k, x, p);
            }
          }

        }

      } else {
        k = arith_var_upper_index(vtbl, x);
        assert(k >= 0);
        xq_add(aux, bstack->bound + k);

#if TRACE_PROPAGATION
        printf("     implied bound: ");
        print_simplex_var(stdout, solver, x);
        printf(" >= ");
        xq_print(stdout, aux);
        printf("\n");
#endif

        if (useful_lower_bound(solver, x, aux)) {
          if (simplex_option_enabled(solver, SIMPLEX_FULLPROP)) {
            w = &solver->aux_vector2;
            assert(w->size == 0);
            all_assertions_implied_by_lb(solver, x, aux, w);
            all_theory_props_from_lower_bounds(solver, w, x, p);
            ivector_reset(w);
          } else {
            k = assertion_implied_by_lb(solver, x, aux);
            if (k >= 0) {
              theory_prop_from_lower_bounds(solver, k, x, p);
            }
          }
        }

      }
    }

    a ++;
    n --;
  } while (n > 0);

#if TRACE_PROPAGATION
  printf("\n");
#endif

}



/*
 * Try propagation based on row p
 */
static void check_row_propagation(simplex_solver_t *solver, row_t *p)  {
  arith_vartable_t *vtbl;
  row_elem_t *a;
  uint32_t n;
  thvar_t x, y;
  int32_t s;

  vtbl = &solver->vtbl;

  y = null_thvar; // variable with no lower bound
  assert(y < 0);
  a = p->data;
  n = p->size;
  do {
    x = a->c_idx;
    if (x >= 0) {
      s = q_sgn(&a->coeff);
      if ((s > 0 && arith_var_lower_index(vtbl, x) < 0) ||
          (s < 0 && arith_var_upper_index(vtbl, x) < 0)) {
        // no lower bound on monomial a.x
        if (y >= 0) goto try_upper_bounds;
        y = x;
      }
    }
    a ++;
    n --;
  } while (n > 0);

  if (y < 0) {
    full_lower_bound_propagation(solver, p);
  } else if (var_has_unassigned_atoms(solver, y)) {
    try_lower_bound_propagation(solver, y, p);
  }

 try_upper_bounds:
  y = null_thvar;
  a = p->data;
  n = p->size;
  do {
    x = a->c_idx;
    if (x >= 0) {
      s = q_sgn(&a->coeff);
      if ((s > 0 && arith_var_upper_index(vtbl, x) < 0) ||
          (s < 0 && arith_var_lower_index(vtbl, x) < 0)) {
        // no upper bound on a.x
        if (y >= 0) goto done;
        y = x;
      }
    }
    a ++;
    n --;
  } while (n > 0);

  if (y < 0) {
    full_upper_bound_propagation(solver, p);
  } else if (var_has_unassigned_atoms(solver, y)) {
    try_upper_bound_propagation(solver, y, p);
  }

 done:
  return;
}



/*
 * Process all rows in the to-process vector
 */
static void check_all_propagation_rows(simplex_solver_t *solver) {
  matrix_t *matrix;
  ivector_t *v;
  row_t *row;
  uint32_t i, n, r;

  matrix = &solver->matrix;
  v = &solver->rows_to_process;
  n = v->size;

#if TRACE_PROPAGATION
  printf("\n---> SIMPLEX PROP: CHECKING %"PRIu32" rows\n", n);
#endif

  for (i=0; i<n; i++) {
    r = v->data[i];
    assert(matrix_row_is_marked(matrix, r));
    matrix_unmark_row(matrix, r);
    row = matrix->row[r];
    if (row->nelems <= solver->prop_row_size) {
      check_row_propagation(solver, row);
    }
  }

#if TRACE_PROPAGATION
  printf("---> END OF SIMPLEX PROPAGATION\n");
#endif

  ivector_reset(v);

  // update prop_ptr in the assertion queue to skip the implied atoms
  solver->assertion_queue.prop_ptr = solver->assertion_queue.top;
}




/*
 * FOR TESTING: try propagation via all rows
 */
static void all_rows_propagation(simplex_solver_t *solver) {
  matrix_t *matrix;
  row_t *row;
  uint32_t i, n;

  matrix = &solver->matrix;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    if (row->nelems <= solver->prop_row_size) {
      check_row_propagation(solver, row);
    }
  }

  // update prop_ptr in the assertion queue to skip the implied atoms
  solver->assertion_queue.prop_ptr = solver->assertion_queue.top;
}





/*
 * FUNCTIONS CALLED FROM simplex.c
 */

/*
 * init_propagator should allocate and initialize the propagator object
 * - solver->propagator is NULL by default
 */
static inline void simplex_init_propagator(simplex_solver_t *solver) {
  // do nothing
}

/*
 * reset_propagator should reset the propagator object
 */
static inline void simplex_reset_propagator(simplex_solver_t *solver) {
  // do nothing
}

/*
 * delete_propagator should reset/delete the propagator object
 */
static inline void simplex_delete_propagator(simplex_solver_t *solver) {
  // do nothing
}


/*
 * start_propagator: called after init_propagator, after the initial tableau is
 * constructed and all initial constraints are found to be feasible.
 */
static void simplex_start_propagator(simplex_solver_t *solver) {
#if 0
  printf("---> after base_level_prop: %"PRIu32" bounds, th-prop = %"PRIu32", prop-lemmas = %"PRIu32" \n",
         solver->bstack.top, solver->stats.num_props, solver->stats.num_prop_lemmas);
  fflush(stdout);
#endif

  // check for implied bounds
  all_rows_propagation(solver);

#if 0
  printf("---> after all_rows_prop: %"PRIu32" bounds, th-prop = %"PRIu32", prop-lemmas = %"PRIu32" \n",
         solver->bstack.top, solver->stats.num_props, solver->stats.num_prop_lemmas);
  fflush(stdout);
#endif
}


/*
 * do_propagation: called in simplex_propagate if propagation is enabled
 */
static void simplex_do_propagation(simplex_solver_t *solver) {
  collect_relevant_prop_rows(solver);
  check_all_propagation_rows(solver);
}


/*
 * explain_propagation: called in simplex_expand_explanation
 */
static void simplex_explain_propagation(simplex_solver_t *solver, literal_t l,
                                        literal_t *expl, ivector_t *v) {
  literal_t l0;

  l0 = *expl ++;
  while (l0 != null_literal) {
    ivector_push(v, l0);
    l0 = *expl ++;
  }
}
