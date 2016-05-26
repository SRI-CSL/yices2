/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/conflict.h"

#include "io/term_printer.h"
#include "mcsat/tracing.h"

#define CONFLICT_DEFAULT_ELEMENT_SIZE 100

/**
 * Add a disjunct to the conflict. The disjunct should evaluate to false in
 * the current trail.
 */
static
bool conflict_add_disjunct(conflict_t* conflict, term_t disjunct);

void conflict_construct(conflict_t* conflict, const ivector_t* conflict_lits,
    const mcsat_evaluator_interface_t* evaluator, variable_db_t* var_db, mcsat_trail_t* trail,
    term_table_t* terms, tracer_t* tracer) {

  uint32_t i;

  conflict->elements_capacity = CONFLICT_DEFAULT_ELEMENT_SIZE;
  conflict->elements_size = 0;
  conflict->elements = safe_malloc(sizeof(conflict_element_t) * CONFLICT_DEFAULT_ELEMENT_SIZE);

  conflict->elements_free_list = conflict_element_ref_null;

  init_int_hmap(&conflict->var_to_element_map, 0);
  int_mset_construct(&conflict->top_level_vars, variable_null);
  int_mset_construct(&conflict->vars_all, variable_null);
  int_mset_construct(&conflict->disjuncts, NULL_TERM);

  conflict->level = 0;
  conflict->top_level_vars_count = 0;

  conflict->var_db = var_db;
  conflict->trail = trail;
  conflict->terms = terms;
  conflict->tracer = tracer;
  conflict->evaluator = evaluator;

  if (conflict_lits) {
    for (i = 0; i < conflict_lits->size; ++ i) {
      conflict_add_disjunct(conflict, opposite_term(conflict_lits->data[i]));
    }
  }
}

void conflict_destruct(conflict_t* conflict) {
  safe_free(conflict->elements);
  delete_int_hmap(&conflict->var_to_element_map);
  int_mset_destruct(&conflict->top_level_vars);
  int_mset_destruct(&conflict->vars_all);
  int_mset_destruct(&conflict->disjuncts);
}

typedef struct {
  const conflict_t* conflict;
  FILE* file;
} conflict_print_data_t;

void conflict_print(const conflict_t* conflict, FILE* out) {
  uint32_t i, n;
  int_hmap_pair_t* data;
  variable_t x;
  conflict_element_ref_t current;

  fprintf(out, "level = %d\n", conflict->level);
  fprintf(out, "top_level_vars = %d\n", conflict->top_level_vars_count);

  fprintf(out, "vars =");
  n = conflict->top_level_vars.element_list.size;
  for (i = 0; i < n; ++ i) {
    variable_t x = conflict->top_level_vars.element_list.data[i];
    if (x != conflict->top_level_vars.null_element && int_mset_contains(&conflict->top_level_vars, x)) {
      fprintf(out, " ");
      variable_db_print_variable(conflict->var_db, x, out);
    }
  }
  fprintf(out, "\n");

  fprintf(out, "disjuncts");

  n = conflict->var_to_element_map.size;
  data = conflict->var_to_element_map.data;
  for (i = 0; i < n; i ++) {
    if (data->key >= 0) {
      x = data->key;
      variable_db_print_variable(conflict->var_db, x, out);
      fprintf(out, " [%d]: ", trail_get_level(conflict->trail, x));
      current = data->val;
      while (current != conflict_element_ref_null) {

        const conflict_element_t* element = conflict->elements + current;

        yices_pp_t printer;
        init_yices_pp(&printer, out, NULL, PP_HMODE, 0);
        pp_term_full(&printer, conflict->terms, element->D);
        flush_pp(&printer.pp, false);
        delete_yices_pp(&printer, false);

        current = element->next;
        if (current != conflict_element_ref_null) {
          fprintf(out, ", ");
        }
      }
      fprintf(out, "\n");
    }
    data ++;
  }
}

static
conflict_element_ref_t conflict_new_element(conflict_t* conflict, term_t disjunct) {

  conflict_element_t* element;
  conflict_element_ref_t element_ref;

  // Check the free list
  if (conflict->elements_free_list != conflict_element_ref_null) {
    // Get from the free list
    element_ref = conflict->elements_free_list;
    element = conflict->elements + element_ref;
    conflict->elements_free_list = element->next;
  } else {
    // Allocate new
    if (conflict->elements_size == conflict->elements_capacity) {
      conflict->elements_capacity = conflict->elements_capacity + (conflict->elements_capacity / 2);
      conflict->elements = safe_realloc(conflict->elements, sizeof(conflict_element_t)*conflict->elements_capacity);
    }
    element_ref = conflict->elements_size ++;
    element = conflict->elements + element_ref;
  }

  // Initialize
  element->D = disjunct;
  element->next = conflict_element_ref_null;

  return element_ref;
}

static inline
void conflict_add_variable(conflict_t* conflict, variable_t var) {
  uint32_t level;

  assert(trail_has_value(conflict->trail, var));
  level = trail_get_level(conflict->trail, var);

  // If construction check the level
  if (level > conflict->level) {
    conflict->level = level;
    conflict->top_level_vars_count = 0;
    int_mset_clear(&conflict->top_level_vars);
  }

  // If first time seen, count if at top level
  if (level == conflict->level) {
    if (!int_mset_contains(&conflict->top_level_vars, var)) {
      conflict->top_level_vars_count ++;
    }
    int_mset_add(&conflict->top_level_vars, var);
  }

  // Add to the variable map
  int_mset_add(&conflict->vars_all, var);
}

static inline
void conflict_remove_variable(conflict_t* conflict, variable_t var) {
  uint32_t level;

  assert(trail_has_value(conflict->trail, var));
  level = trail_get_level(conflict->trail, var);

  // Reduce the variable map
  if (level == conflict->level) {
    int_mset_remove_one(&conflict->top_level_vars, var);
    if (!int_mset_contains(&conflict->top_level_vars, var)) {
      conflict->top_level_vars_count --;
    }
  }
}

static
void conflict_disjunct_get_variables(const conflict_t* conflict, term_t disjunct, int_mset_t* variables) {

  term_t disjunct_pos;
  variable_t disjunct_pos_var;
  bool disjunct_value;
  bool disjunct_evaluates;

  // Positive literal
  disjunct_pos = unsigned_term(disjunct);

  // If the disjunct is true by Boolean assignment then the variable is the
  // variable of the term
  disjunct_pos_var = variable_db_get_variable_if_exists(conflict->var_db, disjunct_pos);
  if (disjunct_pos_var != variable_null && trail_has_value(conflict->trail, disjunct_pos_var)) {
    disjunct_value = trail_get_value(conflict->trail, disjunct_pos_var)->b;
    if (disjunct_pos != disjunct) {
      disjunct_value = !disjunct_value;
    }
    if (!disjunct_value) {
      // Its false, just add the variable
      int_mset_add(variables, disjunct_pos_var);
      return;
    }
  }

  // Get the sub-variables
  disjunct_evaluates = conflict->evaluator->evaluates(conflict->evaluator, disjunct_pos, variables, NULL);
  (void)disjunct_evaluates;
  assert(disjunct_evaluates);
}

static
term_t conflict_disjunct_substitute(const conflict_t* conflict, term_t disjunct, variable_t var, term_t substitution) {

  term_t disjunct_pos, disjunct_subst;
  variable_t disjunct_pos_var;
  bool disjunct_value;

  // Positive literal
  disjunct_pos = unsigned_term(disjunct);

  // If the disjunct is true by Boolean assignment then the variable is the
  // variable of the term
  disjunct_pos_var = variable_db_get_variable_if_exists(conflict->var_db, disjunct_pos);
  if (disjunct_pos_var != variable_null && trail_has_value(conflict->trail, disjunct_pos_var)) {
    disjunct_value = trail_get_value(conflict->trail, disjunct_pos_var)->b;
    if (disjunct_pos != disjunct) {
      disjunct_value = !disjunct_value;
    }
    if (!disjunct_value) {
      // Its false
      assert(disjunct_pos_var == var);
      return bool2term(false);
    }
  }

  // Substitute
  disjunct_subst = variable_db_substitute_subvariable(conflict->var_db, disjunct_pos, var, substitution);
  assert(disjunct_pos != disjunct_subst);
  if (disjunct_pos != disjunct) {
    disjunct_subst = opposite_term(disjunct_subst);
  }
  return disjunct_subst;
}

static
bool conflict_add_disjunct(conflict_t* conflict, term_t disjunct) {

  conflict_element_t* element;
  conflict_element_ref_t element_ref;
  int_hmap_pair_t* find;

  int_mset_t disjunct_vars;
  const ivector_t* disjunct_vars_list;

  uint32_t i;
  variable_t var, top_var;
  uint32_t var_index, var_level;
  uint32_t top_var_index, top_var_level;

  assert(disjunct >= 0);

  if (trace_enabled(conflict->tracer, "mcsat::conflict")) {
    trace_printf(conflict->tracer, "adding to conflict: ");
    trace_term_ln(conflict->tracer, conflict->terms, disjunct);
  }

  // Don't add false
  if (disjunct == bool2term(false)) {
    return false;
  }

  // Check if already there
  if (int_mset_contains(&conflict->disjuncts, disjunct)) {
    return false;
  }

  // Construct of temps
  int_mset_construct(&disjunct_vars, variable_null);

  // Get the variables
  conflict_disjunct_get_variables(conflict, disjunct, &disjunct_vars);

  // Get the top variable by trail index and add the variables
  disjunct_vars_list = int_mset_get_list(&disjunct_vars);
  top_var = variable_null;
  top_var_index = 0;
  top_var_level = 0;
  for (i = 0; i < disjunct_vars_list->size; ++ i) {
    var = disjunct_vars_list->data[i];
    // Add to conflict
    conflict_add_variable(conflict, var);
    // Check if top:
    // - we compare indices, these matter only for resolving propagations
    // - we only need to know what's the next variable to resolve
    // - we just resolve the variables at top level
    // - confusing example: (= x y), level(x) > level(y) but index(y) > level(x)
    // - in above, we don't resolve y, just x
    var_level = trail_get_level(conflict->trail, var);
    var_index = trail_get_index(conflict->trail, var);
    if (top_var == variable_null || var_level > top_var_level || (var_level == top_var_level && var_index > top_var_index)) {
      top_var = var;
      top_var_level = var_level;
      top_var_index = var_index;
    }
  }

  // Allocate an element for the top_var
  element_ref = conflict_new_element(conflict, disjunct);
  element = conflict->elements + element_ref;

  // Find in literal top var -> literal map
  find = int_hmap_find(&conflict->var_to_element_map, top_var);
  if (find == NULL) {
    // Fresh add
    int_hmap_add(&conflict->var_to_element_map, top_var, element_ref);
  } else {
    // Add to the beginning of the list
    element->next = find->val;
    find->val = element_ref;
  }

  // Add to set of disjuncts
  assert(!int_mset_contains(&conflict->disjuncts, disjunct));
  int_mset_add(&conflict->disjuncts, disjunct);

  // Destruction of temps
  int_mset_destruct(&disjunct_vars);

  // Added OK
  return true;
}

void conflict_remove_disjunct(conflict_t* conflict, term_t disjunct) {

  if (trace_enabled(conflict->tracer, "mcsat::conflict")) {
    trace_printf(conflict->tracer, "removing from conflict: ");
    trace_term_ln(conflict->tracer, conflict->terms, disjunct);
  }

  uint32_t i;
  int_mset_t disjunct_vars;
  const ivector_t* disjunct_vars_list;

  assert(disjunct >= 0);
  assert(int_mset_contains(&conflict->disjuncts, disjunct));

  // Construct temps
  int_mset_construct(&disjunct_vars, variable_null);

  // Get the variables
  conflict_disjunct_get_variables(conflict, disjunct, &disjunct_vars);

  // Remove the variables
  disjunct_vars_list = int_mset_get_list(&disjunct_vars);
  for (i = 0; i < disjunct_vars_list->size; ++ i) {
    conflict_remove_variable(conflict, disjunct_vars_list->data[i]);
  }

  // Remove from the set of disjuncts
  int_mset_remove_all(&conflict->disjuncts, disjunct);

  // Destruction of temps
  int_mset_destruct(&disjunct_vars);
}


uint32_t conflict_get_level(const conflict_t* conflict) {
  return conflict->level;
}

bool conflict_contains(const conflict_t* conflict, variable_t var) {
  return int_mset_contains(&conflict->top_level_vars, var);
}

bool conflict_contains_as_top(const conflict_t* conflict, variable_t var) {
  conflict_t* conflict_nonconst = (conflict_t*) conflict;  
  return int_hmap_find(&conflict_nonconst->var_to_element_map, var) != NULL;
}

uint32_t conflict_get_top_level_vars_count(const conflict_t* conflict) {
  return conflict->top_level_vars_count;
}

void conflict_recompute_level_info(conflict_t* conflict) {

  // Make a new conflict
  conflict_t new_conflict;
  conflict_construct(&new_conflict, 0, conflict->evaluator, conflict->var_db, conflict->trail, conflict->terms, conflict->tracer);

  // Put in all the disjuncts
  uint32_t i;
  ivector_t* disjuncts = int_mset_get_list(&conflict->disjuncts);
  for (i = 0; i < disjuncts->size; ++ i) {
    conflict_add_disjunct(&new_conflict, disjuncts->data[i]);
  }

  if (trace_enabled(conflict->tracer, "mcsat::resolve")) {
    trace_printf(conflict->tracer, "old = \n");
    conflict_print(conflict, trace_out(conflict->tracer));
    trace_printf(conflict->tracer, "new = \n");
    conflict_print(&new_conflict, trace_out(conflict->tracer));
  }

  // Swap it in
  conflict_t tmp = *conflict;
  *conflict = new_conflict;
  new_conflict = tmp;
  conflict_destruct(&new_conflict);
}



void conflict_resolve_propagation(conflict_t* conflict, variable_t var, term_t substitution, ivector_t* reasons) {

  if (trace_enabled(conflict->tracer, "mcsat::resolve")) {
    trace_printf(conflict->tracer, "conflict = \n");
    conflict_print(conflict, trace_out(conflict->tracer));
  }

  int_hmap_pair_t* find_var;
  conflict_element_ref_t current_element_ref;
  conflict_element_t* current_element = NULL;

  uint32_t i;
  ivector_t disjuncts;

  init_ivector(&disjuncts, 0);

  // * pop propagation
  // * substitute
  // * remove disjuncts
  // * add substitution

  assert(trail_back(conflict->trail) == var);
  assert(trail_get_assignment_type(conflict->trail, var) == PROPAGATION);

  // Got through all the variables where the resolution variable is top and
  // get the disjuncts
  find_var = int_hmap_find(&conflict->var_to_element_map, var);
  assert(find_var != NULL);
  current_element_ref = find_var->val;
  assert(current_element_ref != conflict_element_ref_null);
  while (current_element_ref != conflict_element_ref_null) {
    current_element = conflict->elements + current_element_ref;
    ivector_push(&disjuncts, current_element->D);
    current_element_ref = current_element->next;
  }
  // Add the list to the free list
  current_element->next = conflict->elements_free_list;
  conflict->elements_free_list = find_var->val;

  // Remove from top variable map
  int_hmap_erase(&conflict->var_to_element_map, find_var);

  // Remove the disjuncts
  for (i = 0; i < disjuncts.size; ++ i) {
    conflict_remove_disjunct(conflict, disjuncts.data[i]);
    if (trace_enabled(conflict->tracer, "mcsat::resolve")) {
      trace_printf(conflict->tracer, "resolving ");
      variable_db_print_variable(conflict->var_db, var, conflict->tracer->file);
      trace_printf(conflict->tracer, " with ");
      trace_term_ln(conflict->tracer, conflict->terms, substitution);
      trace_printf(conflict->tracer, "in :\n");
      trace_term_ln(conflict->tracer, conflict->terms, disjuncts.data[i]);
    }
    disjuncts.data[i] = conflict_disjunct_substitute(conflict, disjuncts.data[i], var, substitution);
    if (trace_enabled(conflict->tracer, "mcsat::resolve")) {
      trace_printf(conflict->tracer, "resolvent ");
      trace_term_ln(conflict->tracer, conflict->terms, disjuncts.data[i]);
    }
  }

  // Pop the trail
  trail_pop_propagation(conflict->trail);

  // Add the substitution disjuncts
  for (i = 0; i < disjuncts.size; ++ i) {
    conflict_add_disjunct(conflict, disjuncts.data[i]);
  }

  // Add the reasons
  for (i = 0; i < reasons->size; ++ i) {
    conflict_add_disjunct(conflict, opposite_term(reasons->data[i]));
  }

  // Destruct temp
  delete_ivector(&disjuncts);

  if (trace_enabled(conflict->tracer, "mcsat::resolve")) {
    trace_printf(conflict->tracer, "conflict = \n");
    conflict_print(conflict, trace_out(conflict->tracer));
  }

}

ivector_t* conflict_get_variables(conflict_t* conflict) {
  return int_mset_get_list(&conflict->top_level_vars);
}

const int_mset_t* conflict_get_variables_all(conflict_t* conflict) {
    return &conflict->vars_all;
}

void conflict_get_literals_of(conflict_t* conflict, variable_t var, ivector_t* literals) {
  int_hmap_pair_t* find;
  conflict_element_ref_t current_ref;
  conflict_element_t* current;
  find = int_hmap_find(&conflict->var_to_element_map, var);
  if (find != NULL) {
    current_ref = find->val;
    while (current_ref != conflict_element_ref_null) {
      current = conflict->elements + current_ref;
      ivector_push(literals, current->D);
      current_ref = current->next;
    }
  }
}

ivector_t* conflict_get_literals(conflict_t* conflict) {
  return int_mset_get_list(&conflict->disjuncts);
}
