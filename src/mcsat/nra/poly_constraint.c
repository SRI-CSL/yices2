/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/nra/poly_constraint.h"
#include "mcsat/nra/libpoly_utils.h"
#include "terms/terms.h"
#include "mcsat/tracing.h"

#include <poly/variable_db.h>
#include <poly/variable_list.h>
#include <poly/feasibility_set.h>

/**
 * A constraint of the form sgn(p(x)) = sgn_conition.
 */
struct poly_constraint_struct {

  /** The polynomial of the constraint */
  lp_polynomial_t* polynomial;

  /** The sign condition */
  lp_sign_condition_t sgn_condition;

  /** If this is a root constraint, this is the variable */
  lp_variable_t x;

  /** If this is a root constraint, this is the root index */
  size_t root_index;
};

static
bool poly_constraint_ok(const poly_constraint_t* cstr) {
  switch (cstr->sgn_condition) {
  case LP_SGN_LT_0:
  case LP_SGN_LE_0:
  case LP_SGN_EQ_0:
  case LP_SGN_NE_0:
  case LP_SGN_GT_0:
  case LP_SGN_GE_0:
    break;
  default:
    return false;
  }
  return lp_polynomial_check_integrity(cstr->polynomial);;
}

/** Database of constraints */
struct poly_constraint_db_struct {
  /** The plugin */
  nra_plugin_t* nra;

  /** Vector of constraints */
  pvector_t constraints;

  /** Map from variables to constraint references */
  int_hmap_t var_to_constraint_map;
};

static
void poly_constraint_gc_mark(const poly_constraint_t* constraint, nra_plugin_t* nra, gc_info_t* gc_vars) {
  lp_variable_list_t vars;
  lp_variable_list_construct(&vars);
  lp_polynomial_get_variables(constraint->polynomial, &vars);
  uint32_t var_i;
  for (var_i = 0; var_i < vars.list_size; ++ var_i) {
    lp_variable_t x_lp = vars.list[var_i];
    variable_t x = nra_plugin_get_variable_from_lp_variable(nra, x_lp);
    gc_info_mark(gc_vars, x);
  }
  lp_variable_list_destruct(&vars);
}

void poly_constraint_db_gc_mark(poly_constraint_db_t* db, gc_info_t* gc_vars) {
  // Look for any constraints at the current gc level
  uint32_t marked_i = 0;
  for (marked_i = gc_vars->marked_first; marked_i < gc_vars->marked.size; marked_i ++) {
    // Current variable
    variable_t constraint_var = gc_vars->marked.data[marked_i];
    // Check if in database
    int_hmap_pair_t* find = int_hmap_find(&db->var_to_constraint_map, constraint_var);
    if (find != NULL) {
      // It's a constraint, mark the variables
      assert(find->val < db->constraints.size);
      poly_constraint_t* constraint = db->constraints.data[find->val];
      if (ctx_trace_enabled(db->nra->ctx, "nra::gc")) {
        ctx_trace_printf(db->nra->ctx, "Marking variables of :");
        poly_constraint_print(constraint, ctx_trace_out(db->nra->ctx));
        ctx_trace_printf(db->nra->ctx, "\n");
      }
      // Mark the variables in the constraint
      poly_constraint_gc_mark(constraint, db->nra, gc_vars);
    }
  }
}

void poly_constraint_db_gc_sweep(poly_constraint_db_t* db, const gc_info_t* gc_vars) {

  pvector_t new_constraints;
  int_hmap_t new_var_to_contraint_map;

  init_pvector(&new_constraints, 0);
  init_int_hmap(&new_var_to_contraint_map, 0);

  // Move the constraints
  int_hmap_pair_t* it = int_hmap_first_record(&db->var_to_constraint_map);
  for (; it != NULL; it = int_hmap_next_record(&db->var_to_constraint_map, it)) {
    // Do we keep it
    variable_t old_constraint_var = it->key;
    variable_t new_constraint_var = gc_info_get_reloc(gc_vars, old_constraint_var);
    poly_constraint_t* constraint = db->constraints.data[it->val];
    if (new_constraint_var != gc_vars->null_value) {
      // Move it
      uint32_t new_index = new_constraints.size;
      pvector_push(&new_constraints, constraint);
      int_hmap_add(&new_var_to_contraint_map, new_constraint_var, new_index);
    } else {
      if (ctx_trace_enabled(db->nra->ctx, "nra::gc")) {
        ctx_trace_printf(db->nra->ctx, "Removing constraint :");
        poly_constraint_print(constraint, ctx_trace_out(db->nra->ctx));
        ctx_trace_printf(db->nra->ctx, "\n");
      }
      // Delete it
      poly_constraint_delete(constraint);
    }
  }

  // Destroy and swap in the new ones
  delete_pvector(&db->constraints);
  delete_int_hmap(&db->var_to_constraint_map);
  db->constraints = new_constraints;
  db->var_to_constraint_map = new_var_to_contraint_map;
}


void poly_constraint_construct_regular(poly_constraint_t* cstr, lp_polynomial_t* p, lp_sign_condition_t sgn_contition) {
  cstr->polynomial = p;
  cstr->sgn_condition = sgn_contition;
  cstr->x = lp_variable_null;
  cstr->root_index = 0;
}

void poly_constraint_construct_root(poly_constraint_t* cstr, lp_polynomial_t* p, lp_sign_condition_t sgn_contition, lp_variable_t x, uint32_t root_index) {
  cstr->polynomial = p;
  cstr->sgn_condition = sgn_contition;
  cstr->x = x;
  cstr->root_index = root_index;
}

poly_constraint_t* poly_constraint_new_regular(lp_polynomial_t* p, lp_sign_condition_t sgn_contition) {
  poly_constraint_t* cstr = safe_malloc(sizeof(poly_constraint_t));
  poly_constraint_construct_regular(cstr, p, sgn_contition);
  lp_polynomial_set_external(p);
  return cstr;
}

poly_constraint_t* poly_constraint_new_root(lp_polynomial_t* p, lp_sign_condition_t sgn_contition, lp_variable_t x, uint32_t root_index) {
  poly_constraint_t* cstr = safe_malloc(sizeof(poly_constraint_t));
  poly_constraint_construct_root(cstr, p, sgn_contition, x, root_index);
  lp_polynomial_set_external(p);
  return cstr;
}

void poly_constraint_destruct(poly_constraint_t* cstr) {
  lp_polynomial_delete(cstr->polynomial);
}

void poly_constraint_delete(poly_constraint_t* cstr) {
  poly_constraint_destruct(cstr);
  safe_free(cstr);
}

void mathematica_print_traverse(const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* data) {
  FILE* out = data;

  fprintf(out, "(");
  lp_integer_print(&m->a, out);
  uint32_t i = 0;
  for (i = 0; i < m->n; ++ i) {
    fprintf(out, "*x%zu^%zu", m->p[i].x, m->p[i].d);
  }
  fprintf(out, ") + ");
}

void poly_constraint_print_mathematica(const poly_constraint_t* cstr, bool negated, FILE* out) {

  if (poly_constraint_is_root_constraint(cstr)) {
    fprintf(out, "(x%zu - ", cstr->x);
    fprintf(out, "Root[");
    lp_polynomial_traverse(cstr->polynomial, mathematica_print_traverse, out);
    fprintf(out, "0, %zu]", cstr->root_index);
    lp_sign_condition_print(cstr->sgn_condition, out);
    fprintf(out, ")");
  } else {
    fprintf(out, "(");
    lp_polynomial_traverse(cstr->polynomial, mathematica_print_traverse, out);
    fprintf(out, "0 ");
    lp_sign_condition_t sgn_condition = cstr->sgn_condition;
    if (negated) {
      sgn_condition = lp_sign_condition_negate(sgn_condition);
    }
    lp_sign_condition_print(sgn_condition, out);
    fprintf(out, ")");
  }
}

void poly_constraint_print(const poly_constraint_t* cstr, FILE* out) {

  const lp_polynomial_context_t* ctx = lp_polynomial_get_context(cstr->polynomial);

  if (poly_constraint_is_root_constraint(cstr)) {
    fprintf(out, "(%s - ", lp_variable_db_get_name(ctx->var_db, cstr->x));
    fprintf(out, "root(%zu, ", cstr->root_index);
    lp_polynomial_print(cstr->polynomial, out);
    fprintf(out, ") ");
    lp_sign_condition_print(cstr->sgn_condition, out);
    fprintf(out, ")");
  } else {
    fprintf(out, "(");
    lp_sign_condition_print(cstr->sgn_condition, out);
    fprintf(out, " (");
    lp_polynomial_print(cstr->polynomial, out);
    fprintf(out, ") 0)");
  }
}

lp_sign_condition_t poly_constraint_get_sign_condition(const poly_constraint_t* cstr) {
  return cstr->sgn_condition;
}

const lp_polynomial_t* poly_constraint_get_polynomial(const poly_constraint_t* cstr) {
  return cstr->polynomial;
}

bool poly_constraint_is_root_constraint(const poly_constraint_t* cstr) {
  return cstr->x != lp_variable_null;
}

lp_variable_t poly_constraint_get_variable(const poly_constraint_t* cstr) {
  return cstr->x;
}

uint32_t poly_constraint_get_root_index(const poly_constraint_t* cstr) {
  return cstr->root_index;
}

lp_feasibility_set_t* poly_constraint_get_feasible_set(const poly_constraint_t* cstr, const lp_assignment_t* m, bool negated) {

  lp_feasibility_set_t* feasible  = 0;

  if (poly_constraint_is_root_constraint(cstr)) {
    // Get the root constraint feasible set
    if (cstr->x != lp_polynomial_top_variable(cstr->polynomial)) {
      // x not top => constraint ignored
      feasible = lp_feasibility_set_new_full();
    } else {
      feasible = lp_polynomial_root_constraint_get_feasible_set(cstr->polynomial, cstr->root_index, cstr->sgn_condition, negated, m);
    }
  } else {
    // Get the polynomial feasible set
    feasible = lp_polynomial_constraint_get_feasible_set(cstr->polynomial, cstr->sgn_condition, negated, m);
  }

  return feasible;
}

lp_variable_t poly_constraint_get_top_variable(const poly_constraint_t* cstr) {
  return lp_polynomial_top_variable(cstr->polynomial);
}

void poly_constraint_db_construct(poly_constraint_db_t* db, nra_plugin_t* nra) {
  db->nra = nra;

  init_pvector(&db->constraints, 0);
  init_int_hmap(&db->var_to_constraint_map, 0);
}

poly_constraint_db_t* poly_constraint_db_new(nra_plugin_t* nra) {
  poly_constraint_db_t* db;
  db = safe_malloc(sizeof(poly_constraint_db_t));
  poly_constraint_db_construct(db, nra);
  return db;
}

void poly_constraint_db_destruct(poly_constraint_db_t* db) {
  uint32_t i;
  poly_constraint_t* cstr;

  for (i = 0; i < db->constraints.size; i ++) {
    cstr = db->constraints.data[i];
    poly_constraint_delete(cstr);
  }

  delete_pvector(&db->constraints);
  delete_int_hmap(&db->var_to_constraint_map);
}

void poly_constraint_db_delete(poly_constraint_db_t* db) {
  poly_constraint_db_destruct(db);
  safe_free(db);
}

bool poly_constraint_db_check(const poly_constraint_db_t* db) {
  uint32_t i;
  for (i = 0; i < db->constraints.size; ++ i) {
    if (!poly_constraint_ok(db->constraints.data[i])) {
      return false;
    }
  }
  return true;
}

const poly_constraint_t* poly_constraint_db_get(poly_constraint_db_t* db, variable_t constraint_var) {

  if (TRACK_CONSTRAINT(constraint_var)) {
    fprintf(stderr, "Getting tracked constraint:\n");
    variable_db_print_variable(db->nra->ctx->var_db, constraint_var, stderr);
    fprintf(stderr, "\n");
  }

  // assert(poly_constraint_db_check(db));
  int_hmap_pair_t* find;
  find = int_hmap_find(&db->var_to_constraint_map, constraint_var);
  assert(find != NULL);
  assert(find->val < db->constraints.size);
  poly_constraint_t* constraint = db->constraints.data[find->val];
  // assert(poly_constraint_ok(constraint));
  // assert(poly_constraint_db_check(db));
  return constraint;
}

void poly_constraint_db_add(poly_constraint_db_t* db, variable_t constraint_var) {
  // assert(poly_constraint_db_check(db));

  if (int_hmap_find(&db->var_to_constraint_map, constraint_var) != NULL) {
    // Already added
    return;
  }

  term_t t1, t2;
  term_kind_t kind;
  term_t constraint_var_term;

  if (TRACK_CONSTRAINT(constraint_var)) {
    fprintf(stderr, "Tracked constraint added:\n");
    variable_db_print_variable(db->nra->ctx->var_db, constraint_var, stderr);
    fprintf(stderr, "\n");
  }

  // Constraint components
  lp_polynomial_t* cstr_polynomial = 0;
  lp_variable_t cstr_root_variable = lp_variable_null;
  uint32_t cstr_root_index = 0;
  lp_sign_condition_t sgn_condition;

  // Result constraint
  poly_constraint_t* cstr;

  // Context
  variable_db_t* var_db = db->nra->ctx->var_db;
  term_table_t* terms = db->nra->ctx->terms;

  // Get the term of the variable
  constraint_var_term = variable_db_get_term(var_db, constraint_var);

  // Depending on the kind, make the constraints
  kind = term_kind(terms, constraint_var_term);
  switch (kind) {
  case ARITH_EQ_ATOM: {
    // p == 0
    t1 = arith_atom_arg(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term(db->nra, terms, t1, NULL);
    sgn_condition = LP_SGN_EQ_0;
    break;
  }
  case ARITH_GE_ATOM:
    // p >= 0
    t1 = arith_atom_arg(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term(db->nra, terms, t1, NULL);
    sgn_condition = LP_SGN_GE_0;
    break;
  case ARITH_BINEQ_ATOM: {
    // LHS = RHS
    t1 = composite_term_arg(terms, constraint_var_term, 0);
    t2 = composite_term_arg(terms, constraint_var_term, 1);
    // Get the polynomials
    lp_integer_t t1_c, t2_c;
    lp_integer_construct(&t1_c);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_from_term(db->nra, terms, t1, &t1_c);
    lp_polynomial_t* t2_p = lp_polynomial_from_term(db->nra, terms, t2, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    // Add them
    cstr_polynomial = lp_polynomial_new(db->nra->lp_data.lp_ctx);
    lp_polynomial_add(cstr_polynomial, t1_p, t2_p);
    // p1 = p2
    sgn_condition = LP_SGN_EQ_0;
    // Remove temps
    lp_polynomial_delete(t1_p);
    lp_polynomial_delete(t2_p);
    lp_integer_destruct(&t1_c);
    lp_integer_destruct(&t2_c);
    break;
  }
  case ARITH_ROOT_ATOM: {
    root_atom_t* r = arith_root_atom_desc(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term(db->nra, terms, r->p, NULL);
    variable_t x = variable_db_get_variable_if_exists(db->nra->ctx->var_db, r->x);
    assert(x != variable_null);
    cstr_root_variable = nra_plugin_get_lp_variable(db->nra, x);
    cstr_root_index = r->k;
    switch (r->r) {
    case ROOT_ATOM_LT:
      sgn_condition = LP_SGN_LT_0;
      break;
    case ROOT_ATOM_LEQ:
      sgn_condition = LP_SGN_LE_0;
      break;
    case ROOT_ATOM_EQ:
      sgn_condition = LP_SGN_EQ_0;
      break;
    case ROOT_ATOM_NEQ:
      sgn_condition = LP_SGN_NE_0;
      break;
    case ROOT_ATOM_GEQ:
      sgn_condition = LP_SGN_GE_0;
      break;
    case ROOT_ATOM_GT:
      sgn_condition = LP_SGN_GT_0;
      break;
    default:
      sgn_condition = LP_SGN_EQ_0;
      assert(false);
      break;
    }
    break;
  }
  default: {
    // terms like (x+y), we create regular constraint (x+y) = x + y
    lp_integer_t t1_c, t2_c;
    lp_integer_construct_from_int(lp_Z, &t1_c, 1);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_alloc();
    lp_variable_t constraint_lp_var = nra_plugin_get_lp_variable(db->nra, constraint_var);
    lp_polynomial_construct_simple(t1_p, db->nra->lp_data.lp_ctx, &t1_c, constraint_lp_var, 1);
    lp_polynomial_t* t2_p = lp_polynomial_from_term(db->nra, terms, constraint_var_term, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    // Add them
    cstr_polynomial = lp_polynomial_new(db->nra->lp_data.lp_ctx);
    lp_polynomial_add(cstr_polynomial, t1_p, t2_p);
    // p1 = p2
    sgn_condition = LP_SGN_EQ_0;
    // Remove temps
    lp_polynomial_delete(t1_p);
    lp_polynomial_delete(t2_p);
    lp_integer_destruct(&t1_c);
    lp_integer_destruct(&t2_c);

    break;
  }
  }

  // Id of the new constraint
  uint32_t index = db->constraints.size;

  // Create the appropriate constraint
  if (cstr_root_variable == lp_variable_null) {
    cstr = poly_constraint_new_regular(cstr_polynomial, sgn_condition);
  } else {
    cstr = poly_constraint_new_root(cstr_polynomial, sgn_condition, cstr_root_variable, cstr_root_index);
  }

  if (ctx_trace_enabled(db->nra->ctx, "mcsat::new_term")) {
    ctx_trace_printf(db->nra->ctx, "poly_constraint_add: ");
    poly_constraint_print(cstr, ctx_trace_out(db->nra->ctx));
    ctx_trace_printf(db->nra->ctx, "\n");
  }

  assert(poly_constraint_ok(cstr));

  // Add the constraint
  pvector_push(&db->constraints, cstr);
  int_hmap_add(&db->var_to_constraint_map, constraint_var, index);

  // assert(poly_constraint_db_check(db));
}

const mcsat_value_t* poly_constraint_evaluate(const poly_constraint_t* cstr, const variable_t* var_list, nra_plugin_t* nra, uint32_t* cstr_level) {

  bool eval;

  assert(poly_constraint_ok(cstr));

  // Evaluate
  if (poly_constraint_is_root_constraint(cstr)) {
    if (cstr->x != lp_polynomial_top_variable(cstr->polynomial)) {
      // if not top, ignore
      return NULL;
    } else {
      eval = lp_polynomial_root_constraint_evaluate(cstr->polynomial, cstr->root_index, cstr->sgn_condition, nra->lp_data.lp_assignment);
    }
  } else {
    eval = lp_polynomial_constraint_evaluate(cstr->polynomial, cstr->sgn_condition, nra->lp_data.lp_assignment);
  }

  // Get the variables if not there
  if (var_list == NULL) {
    lp_variable_list_t cstr_vars;
    lp_variable_list_construct(&cstr_vars);
    lp_polynomial_get_variables(cstr->polynomial, &cstr_vars);
    *cstr_level = 0;
    uint32_t i;
    for (i = 0; i < cstr_vars.list_size; ++i) {
      variable_t x = nra_plugin_get_variable_from_lp_variable(nra,
          cstr_vars.list[i]);
      uint32_t l = trail_get_level(nra->ctx->trail, x);
      if (l > *cstr_level) {
        *cstr_level = l;
      }
    }
    lp_variable_list_destruct(&cstr_vars);
  } else {
    // Compute the level
    *cstr_level = 0;
    while (*var_list != variable_null) {
      uint32_t l = trail_get_level(nra->ctx->trail, *var_list);
      if (l > *cstr_level) {
        *cstr_level = l;
      }
      var_list++;
    }
  }

  return eval ? &mcsat_value_true : &mcsat_value_false;
}
