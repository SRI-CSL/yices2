/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SIMPLEX PROPAGATOR
 *
 * Revised version of a baseline propagator (11/03/2008)
 * Try to imitate Yices 1
 */


/*
 * The propagator can use solver->propagator as a pointer to any object it needs.
 *
 * The propagator interface consists of the following functions:
 * 1) simplex_init_propagator
 *    called in start search after simplify_matrix but before the tableau is constructed
 *    and checked for feasibility
 * 2) simplex_start_propagator
 *    called in start_search after the tableau is constructed, feasible, and all initial
 *    bounds  are known
 * 3) simplex_reset_propagator: called in simplex_reset and simplex_reset_tableau
 * 4) simplex_delete_propagator: called in delete_simplex_solver
 * 5) simplex_do_propagation: called in simplex_propagate if the tableau is feasible
 */


/*
 * Compile-time option:
 * - ROW_SELECTION: which rows are visited in do_propagation
 *   possible values are 0, 1, and 2
 *   0) only the last conflict row
 *   1) all rows that contain a variable whose lower or upper bound has changed
 *   2) all the rows
 * - TRANSITIVE_PROPAGATION: do we do transitive propagation
 *   0) NO: a derived bound is not used as antecedent in a bound propagation
 *   1) YES: derived bound can be used as antecedents
 * - ALL_DERIVED_BOUNS: what gets propagated (what's considered useful)
 *   possible values are 0 or 1
 *   0) any derived bound that implies at least one literal
 *   1) any derived bound whether or not it implies a literal
 */
#define ROW_SELECTION          1
#define TRANSITIVE_PROPAGATION 1
#define ALL_DERIVED_BOUNDS     0


/*
 * Turn row selection into boolean flags
 */
#define VISIT_LAST_CONFLICT_ROW (ROW_SELECTION == 0)
#define VISIT_AFFECTED_ROWS     (ROW_SELECTION == 1)
#define VISIT_ALL_ROWS          (ROW_SELECTION == 2)


/*
 * Encode this into a propagation level
 * lower level means less propagation
 * - the minimal level is 0
 * - the maximal level is 11
 */

#define PROP_LEVEL (4*ROW_SELECTION + 2*TRANSITIVE_PROPAGATION + ALL_DERIVED_BOUNDS)

#if PROP_LEVEL == 11
const char * const simplex_prop_level = "prop level 11";
#elif PROP_LEVEL == 10
const char * const simplex_prop_level = "prop level 10";
#elif PROP_LEVEL == 9
const char * const simplex_prop_level = "prop level 09";
#elif PROP_LEVEL == 8
const char * const simplex_prop_level = "prop level 08";
#elif PROP_LEVEL == 7
const char * const simplex_prop_level = "prop level 07";
#elif PROP_LEVEL == 6
const char * const simplex_prop_level = "prop level 06";
#elif PROP_LEVEL == 5
const char * const simplex_prop_level = "prop level 05";
#elif PROP_LEVEL == 4
const char * const simplex_prop_level = "prop level 04";
#elif PROP_LEVEL == 3
const char * const simplex_prop_level = "prop level 03";
#elif PROP_LEVEL == 2
const char * const simplex_prop_level = "prop level 02";
#elif PROP_LEVEL == 1
const char * const simplex_prop_level = "prop level 01";
#elif PROP_LEVEL == 0
const char * const simplex_prop_level = "prop level 00";
#else
const char * const simplex_prop_level = "prop level ??";
#endif







/*
 * WHICH VARIABLE/LITERALS ARE CANDIDATE FOR PROPAGATION
 */


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



#if ALL_DERIVED_BOUNDS

/*
 * Bound x >= b is accepted as derived bound if it's better than the existing lower bound on x
 */
static inline bool useful_derived_lb(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  return improved_lower_bound(solver, x, b);
}

/*
 * Bound x <= b is accepted if it's better than the existing upper bound on x
 */
static inline bool useful_derived_ub(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  return improved_upper_bound(solver, x, b);
}


#else



/*
 * Check whether bound x >= b can propagate a literal in the core
 */
static bool lb_can_propagate_literals(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom;
  uint32_t i, n;
  int32_t k;

  atbl = &solver->atbl;
  atom_vector = arith_var_atom_vector(&solver->vtbl, x);
  if (atom_vector != NULL) {
    n = iv_size(atom_vector);
    for (i=0; i<n; i++) {
      k = atom_vector[i];
      if (arith_atom_is_unmarked(atbl, k)) {
        // k is not already assigned
        atom = arith_atom(atbl, k);
        assert(var_of_atom(atom) == x);
        if (atom_is_ge(atom)) {
          /*
           * Atom k is (x >= c)
           * (x >= b) implies (x >= c) if b >= c
           */
          if (xq_ge_q(b, bound_of_atom(atom))) return true;
        } else {
          /*
           * Atom k is (x <= c)
           * (x >= b) implies (not (x <= c)) if b > c
           */
          assert(atom_is_le(atom));
          if (xq_gt_q(b, bound_of_atom(atom))) return true;
        }
      }
    }
  }

  return false;
}


/*
 * Check whether bound x <= b can propagate a literal in the core
 */
static bool ub_can_propagate_literals(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom;
  uint32_t i, n;
  int32_t k;

  atbl = &solver->atbl;
  atom_vector = arith_var_atom_vector(&solver->vtbl, x);
  if (atom_vector != NULL) {
    n = iv_size(atom_vector);
    for (i=0; i<n; i++) {
      k = atom_vector[i];
      if (arith_atom_is_unmarked(atbl, k)) {
        // k is not already assigned
        atom = arith_atom(atbl, k);
        assert(var_of_atom(atom) == x);
        if (atom_is_ge(atom)) {
          /*
           * Atom k is (x >= c)
           * (x <= b) implies (not (x >= c)) if b < c
           */
          if (xq_lt_q(b, bound_of_atom(atom))) return true;
        } else {
          /*
           * Atom k is (x <= c)
           * (x <= b) implies (x <= c) if b <= c
           */
          assert(atom_is_le(atom));
          if (xq_le_q(b, bound_of_atom(atom))) return true;
        }
      }
    }
  }

  return false;
}



/*
 * Bound x >= b is accepted as derived bound if it's better than the existing lower bound on x
 * and can propagate a literal
 */
static inline bool useful_derived_lb(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  return improved_lower_bound(solver, x, b) && lb_can_propagate_literals(solver, x, b);
}

/*
 * Bound x <= b is accepted if it's better than the existing upper bound on x
 */
static inline bool useful_derived_ub(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  return improved_upper_bound(solver, x, b) && ub_can_propagate_literals(solver, x, b);
}


#endif



/*
 * Check whether bound k is a derived bound
 */
static inline bool is_derived_bound(simplex_solver_t *solver, int32_t k) {
  assert(0 <= k && k < solver->bstack.top);
  return arith_tag_get_expl(solver->bstack.tag[k]) == AEXPL_DERIVED;
}




/*
 * Variable filter
 */
#if TRANSITIVE_PROPAGATION

static inline bool good_lb_antecedent(simplex_solver_t *solver, thvar_t x) {
  return arith_var_lower_index(&solver->vtbl, x) >= 0;
}

static inline bool good_ub_antecedent(simplex_solver_t *solver, thvar_t x) {
  return arith_var_upper_index(&solver->vtbl, x) >= 0;
}

#else

static inline bool good_lb_antecedent(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 && ! is_derived_bound(solver, k);
}

static inline bool good_ub_antecedent(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 && ! is_derived_bound(solver, k);
}


#endif




/*
 * CORE PROPAGATION PROCEDURES
 */

/*
 * Explain the upper bounds on all monomials of p
 * - skip the monomial that contains variable x
 * - the explanations are bound indices stored in vector v
 * - explanation for a.y <= c is the current upper index on y if a>0
 *                            or the current lower index on y if a<0
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
 * PROPAGATION BASED ON A ROW OF THE TABLEAU
 */

/*
 * Compute the bound implied on y by the other variables of p
 * - all monomials must have an upper bound except a.y
 * - return false if a conflict is detected, true otherwise
 */
static bool try_upper_bound_propagation(simplex_solver_t *solver, thvar_t y, row_t *p)  {
  row_elem_t *a;
  xrational_t *bound, *sum;
  rational_t *c; // coefficient of y in p
  arith_vartable_t *vtbl;
  ivector_t *v;
  uint32_t n;
  thvar_t x;
  int32_t k;
  bool ok;

#if TRACE_PROPAGATION
  printf("\n---> try_upper_bound_propagation for ");
  print_simplex_var(stdout, solver, y);
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  ok = true;

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
    fflush(stdout);
#endif

    if (useful_derived_lb(solver, y, sum)) {
      v = &solver->aux_vector;
      assert(v->size == 0);
      explain_upper_bounds(solver, y, p, v);
      ok = simplex_add_derived_lower_bound(solver, y, sum, v);
      ivector_reset(v);

#if TRACE_THEORY
      trace_simplex_implied_lb(p, y, sum);
#endif
    }

  } else {

#if TRACE_PROPAGATION
    printf("     implied bound: ");
    print_simplex_var(stdout, solver, y);
    printf(" <= ");
    xq_print(stdout, sum);
    printf("\n");
    fflush(stdout);
#endif

    if (useful_derived_ub(solver, y, sum)) {
      v = &solver->aux_vector;
      assert(v->size == 0);
      explain_upper_bounds(solver, y, p, v);
      ok = simplex_add_derived_upper_bound(solver, y, sum, v);
      ivector_reset(v);

#if TRACE_THEORY
      trace_simplex_implied_ub(p, y, sum);
#endif
    }

  }

  return ok;
}


/*
 * Compute the bound implied on y by the other variables of p
 * - all monomials must have an lower bound except a.y
 * - return false if a conflict is detected, true otherwise
 */
static bool try_lower_bound_propagation(simplex_solver_t *solver, thvar_t y, row_t *p) {
  row_elem_t *a;
  xrational_t *bound, *sum;
  rational_t *c; // coefficient of y in p
  arith_vartable_t *vtbl;
  ivector_t *v;
  uint32_t n;
  thvar_t x;
  int32_t k;
  bool ok;

#if TRACE_PROPAGATION
  printf("\n---> try_lower_bound_propagation for ");
  print_simplex_var(stdout, solver, y);
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  ok = true;

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
    fflush(stdout);
#endif

    if (useful_derived_ub(solver, y, sum)) {
      v = &solver->aux_vector;
      assert(v->size == 0);
      explain_lower_bounds(solver, y, p, v);
      ok = simplex_add_derived_upper_bound(solver, y, sum, v);
      ivector_reset(v);

#if TRACE_THEORY
      trace_simplex_implied_ub(p, y, sum);
#endif
    }

  } else {

#if TRACE_PROPAGATION
    printf("     implied bound: ");
    print_simplex_var(stdout, solver, y);
    printf(" >= ");
    xq_print(stdout, sum);
    printf("\n");
    fflush(stdout);
#endif

    if (useful_derived_lb(solver, y, sum)) {
      v = &solver->aux_vector;
      assert(v->size == 0);
      explain_lower_bounds(solver, y, p, v);
      ok = simplex_add_derived_lower_bound(solver, y, sum, v);
      ivector_reset(v);

#if TRACE_THEORY
      trace_simplex_implied_lb(p, y, sum);
#endif
    }

  }

  return ok;
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
 * - all monomials must have a loweer bound
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
 * - return false if a conflict is detected, true otherwise.
 */
static bool full_upper_bound_propagation(simplex_solver_t *solver, row_t *p) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  xrational_t *sum, *aux;
  row_elem_t *a;
  ivector_t *v;
  uint32_t n;
  thvar_t x;
  int32_t k;
  bool ok;

#if TRACE_PROPAGATION
  printf("\n---> full_upper_bound_propagation");
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  ok = true;

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
        fflush(stdout);
#endif

        if (useful_derived_lb(solver, x, aux)) {
          v = &solver->aux_vector;
          assert(v->size == 0);
          explain_upper_bounds(solver, x, p, v);
          ok = simplex_add_derived_lower_bound(solver, x, aux, v);
          ivector_reset(v);

#if TRACE_THEORY
          trace_simplex_implied_lb(p, x, aux);
#endif
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
        fflush(stdout);
#endif

        if (useful_derived_ub(solver, x, aux)) {
          v = &solver->aux_vector;
          assert(v->size == 0);
          explain_upper_bounds(solver, x, p, v);
          ok = simplex_add_derived_upper_bound(solver, x, aux, v);
          ivector_reset(v);

#if TRACE_THEORY
          trace_simplex_implied_ub(p, x, aux);
#endif
        }
      }


    }
    a ++;
    n --;
  } while (n > 0 && ok);

#if TRACE_PROPAGATION
  printf("\n");
#endif

  return ok;
}


/*
 * Try propagation for row p when all monomials have a lower bound
 * - return false is a conflict is detected, true otherwise
 */
static bool full_lower_bound_propagation(simplex_solver_t *solver, row_t *p) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  xrational_t *sum, *aux;
  row_elem_t *a;
  ivector_t *v;
  uint32_t n;
  thvar_t x;
  int32_t k;
  bool ok;

#if TRACE_PROPAGATION
  printf("\n---> full_lower_bound_propagation");
  printf("\n     ");
  print_simplex_row(stdout, solver, p);
  printf("\n");
#endif

  ok = true; // means no conflict

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
        fflush(stdout);
#endif

        if (useful_derived_ub(solver, x, aux)) {
          v = &solver->aux_vector;
          assert(v->size == 0);
          explain_lower_bounds(solver, x, p, v);
          ok = simplex_add_derived_upper_bound(solver, x, aux, v);
          ivector_reset(v);

#if TRACE_THEORY
          trace_simplex_implied_ub(p, x, aux);
#endif
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
        fflush(stdout);
#endif

        if (useful_derived_lb(solver, x, aux)) {
          v = &solver->aux_vector;
          assert(v->size == 0);
          explain_lower_bounds(solver, x, p, v);
          ok = simplex_add_derived_lower_bound(solver, x, aux, v);
          ivector_reset(v);

#if TRACE_THEORY
          trace_simplex_implied_lb(p, x, aux);
#endif

        }

      }
    }

    a ++;
    n --;
  } while (n > 0 && ok);

#if TRACE_PROPAGATION
  printf("\n");
#endif

  return ok;
}




/*
 * PROPAGATION BASED ON A ROW
 */

/*
 * Try propagation based on row p
 * - return false if a conflict is detected, true otherwise
 */
static bool check_row_propagation(simplex_solver_t *solver, row_t *p)  {
  arith_vartable_t *vtbl;
  row_elem_t *a;
  uint32_t n;
  thvar_t x, y;
  int32_t s;
  bool ok;

  vtbl = &solver->vtbl;

  ok = true;

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
    ok = full_lower_bound_propagation(solver, p);
  } else if (var_has_unassigned_atoms(solver, y)) {
    ok = try_lower_bound_propagation(solver, y, p);
  }
  if (! ok) goto done;

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
    ok = full_upper_bound_propagation(solver, p);
  } else if (var_has_unassigned_atoms(solver, y)) {
    ok = try_upper_bound_propagation(solver, y, p);
  }

 done:
  return ok;
}





/*
 * COLLECT ROWS THAT WILL BE ANALYZED FOR PROPAGATION
 */

/*
 * 1) Function collect relevant_prop_rows must be defined if the row-selection
 *    mode is either last-conflict row or affected rows. If stores the
 *    rows to visit into the row_to_process_vector.
 */

#if VISIT_LAST_CONFLICT_ROW

/*
 * Add the last conflict row (if it's known) to the row_to_process vector
 */
static void collect_relevant_prop_rows(simplex_solver_t *solver) {
  matrix_t *matrix;
  int32_t r;

  matrix = &solver->matrix;

  assert(solver->rows_to_process.size == 0);

  r = solver->last_conflict_row;
  if (r >= 0 && matrix_row_is_unmarked(matrix, r)) {
    ivector_push(&solver->rows_to_process, r);
    matrix_mark_row(matrix, r);
  }
}


#elif VISIT_AFFECTED_ROWS

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
  column_t *col;
  uint32_t i;
  thvar_t x;
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
}

#endif





/*
 * VISIT ALL CANDIDATE ROWS
 */


#if VISIT_LAST_CONFLICT_ROW || VISIT_AFFECTED_ROWS

/*
 * Process all rows in the to-process vector
 * - return false if a conflict is detected, true otherwise
 */
static bool visit_candidate_rows(simplex_solver_t *solver) {
  matrix_t *matrix;
  ivector_t *v;
  row_t *row;
  uint32_t i, n, r;
  bool ok;

  ok = true;

  matrix = &solver->matrix;
  v = &solver->rows_to_process;
  n = v->size;

#if TRACE_PROPAGATION
  printf("\n---> SIMPLEX PROP: CHECKING %"PRIu32" rows\n", n);
#endif

  for (i=0; i<n; i++) {
    r = v->data[i];
    assert(matrix_row_is_marked(matrix, r));
    row = matrix->row[r];
    if (row->nelems <= solver->prop_row_size) {
      if (! check_row_propagation(solver, row)) {
        // conflict: return immediately
#if TRACE_PROPAGATION
        printf("---> END OF SIMPLEX PROPAGATION: CONFLICT DETECTED\n");
#endif
        ok = false;
        goto done;
      }
    }
  }

#if TRACE_PROPAGATION
  printf("---> END OF SIMPLEX PROPAGATION\n");
#endif

 done:
  // clear the marks and empty the rows_to_process vector
  for (i=0; i<n; i++) {
    matrix_unmark_row(matrix, v->data[i]);
  }
  ivector_reset(v);

  return ok;
}



#else

// MODE must be VISIT_ALL_ROWS here

/*
 * Go through all the rows
 */
static bool visit_candidate_rows(simplex_solver_t *solver) {
  matrix_t *matrix;
  row_t *row;
  uint32_t i, n;

  matrix = &solver->matrix;
  n = matrix->nrows;

#if TRACE_PROPAGATION
  printf("\n---> SIMPLEX PROP: CHECKING %"PRIu32" rows\n", n);
#endif

  for (i=0; i<n; i++) {
    row = matrix->row[i];
    if (row->nelems <= solver->prop_row_size) {
      if (! check_row_propagation(solver, row)) {
#if TRACE_PROPAGATION
        printf("---> END OF SIMPLEX PROPAGATION: CONFLICT DETECTED\n");
#endif
        return false;
      }
    }
  }

#if TRACE_PROPAGATION
  printf("---> END OF SIMPLEX PROPAGATION\n");
#endif

  return true;
}

#endif





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
static inline void simplex_start_propagator(simplex_solver_t *solver) {
  // do nothing
}


/*
 * do_propagation: called in simplex_propagate if propagation is enabled
 * - it must return false if propagation detects a conflict
 */
static bool simplex_do_propagation(simplex_solver_t *solver) {
#if VISIT_LAST_CONFLICT_ROW || VISIT_AFFECTED_ROWS
  collect_relevant_prop_rows(solver);
#endif
  return visit_candidate_rows(solver);
}


