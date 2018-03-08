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
 
#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/bv/bv_feasible_set_db.h"
#include "mcsat/bv/bv_bdd.h"
#include "mcsat/bv/bv_domain.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/tracing.h"
#include "mcsat/value.h"

#include "utils/int_array_sort.h"

#include "yices.h"

#include <cudd.h>

/**
 * Element in the list. Each element contains a pointer to the previous
 * version, the reason for the update/
 */
typedef struct {

  /** Current domain. */
  bv_domain_t* domain;

  /** Previous version of this (next element in list). 0 if end of list. */
  uint32_t prev;

  /** Reason for latest update. NULL if initial*/
  term_t* reason;
  /** BDD of reason (was computed once, so this is cached). */
  bdds_t* reason_bdd;
  
} bv_feasible_list_element_t;


struct bv_feasible_set_db_struct {

  /** BDD manager */
  DdManager* manager;
  
  /** Elements of the lists */
  bv_feasible_list_element_t* memory;

  /** The currently occupied memory size */
  uint32_t memory_size;

  /** The capacity of the memory */
  uint32_t memory_capacity;

  /** Map from variables to the first element (current feasible set) */
  int_hmap_t var_to_eq_set_map;

  /** Variables that were updated, so we can backtrack */
  ivector_t updates;

  /** All variables that were fixed */
  ivector_t fixed_variables;

  /** Index into the fixed variables */
  uint32_t fixed_variables_i;

  /** Scope for push/pop */
  scope_holder_t scope;

  /** The plugin context */
  plugin_context_t* ctx;

};

DdManager* bv_feasible_set_db_get_bdd_manager(bv_feasible_set_db_t* db){
  return db->manager;
}

static
uint32_t bv_feasible_set_db_get_index(bv_feasible_set_db_t* db, variable_t x) {
  int_hmap_pair_t* find = int_hmap_find(&db->var_to_eq_set_map, x);
  if (find == NULL) {
    return 0;
  } else {
    return find->val;
  }
}

void bv_feasible_set_db_print_var(bv_feasible_set_db_t* db, variable_t var, FILE* out) {
  fprintf(out, "Feasible sets of ");
  variable_db_print_variable(db->ctx->var_db, var, out);
  fprintf(out, " :\n");
  uint32_t index = bv_feasible_set_db_get_index(db, var);
  while (index != 0) {
    bv_feasible_list_element_t* current = db->memory + index;
    /* fprintf(out, "\t%d\n", current->value); */
    bv_domain_print(current->domain);
    if (current->reason != NULL){
      fprintf(out, "\t\tDue to ");
      term_print_to_file(out, db->ctx->terms, current->reason[0]);
      /* if (term_type_kind(db->terms, reason) == BOOL_TYPE) { */
      /*   // Otherwise it's a term evaluation, always true */
      /*   fprintf(out, " assigned to %s\n", trail_get_boolean_value(db->trail, current->reason) ? "true" : "false"); */
      /* } */
    }
    index = current->prev;
  }
}

void bv_feasible_set_db_print(bv_feasible_set_db_t* db, FILE* out) {

  int_hmap_pair_t* it;
  for (it = int_hmap_first_record(&db->var_to_eq_set_map); it != NULL; it = int_hmap_next_record(&db->var_to_eq_set_map, it)) {

    variable_t var = it->key;
    fprintf(out, "Feasible sets of ");
    variable_db_print_variable(db->ctx->var_db, var, out);
    fprintf(out, " :\n");
    if (trail_has_value(db->ctx->trail, var)) {
      fprintf(out, "\tassigned to: ");
      const mcsat_value_t* var_value = trail_get_value(db->ctx->trail, var);
      mcsat_value_print(var_value, out);
      fprintf(out, "\n");
    }

    bv_feasible_set_db_print_var(db, var, out);
  }
}

#define INITIAL_DB_SIZE 100

bv_feasible_set_db_t* bv_feasible_set_db_new(plugin_context_t* ctx) {

  if (ctx_trace_enabled(ctx, "bv_plugin")) {
    ctx_trace_printf(ctx, "bv_feasible_set_db_new(...)\n");
  }

  bv_feasible_set_db_t* db = safe_malloc(sizeof(bv_feasible_set_db_t));

  db->manager = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS,0);

  db->memory_size = 1; // 0 is special null ref
  db->memory_capacity = INITIAL_DB_SIZE;
  db->memory = safe_malloc(sizeof(bv_feasible_list_element_t)*db->memory_capacity);

  init_int_hmap(&db->var_to_eq_set_map, 0);
  init_ivector(&db->updates, 0);
  init_ivector(&db->fixed_variables, 0);

  db->fixed_variables_i = 0;

  scope_holder_construct(&db->scope);

  db->ctx = ctx;

  return db;
}

void bv_feasible_set_db_delete(bv_feasible_set_db_t* db) {

  if (ctx_trace_enabled(db->ctx, "bv_plugin")) {
    ctx_trace_printf(db->ctx, "bv_feasible_set_db_delete(...)\n");
  }

  Cudd_Quit(db->manager);
  delete_int_hmap(&db->var_to_eq_set_map);
  delete_ivector(&db->updates);
  delete_ivector(&db->fixed_variables);
  scope_holder_destruct(&db->scope);
  // Free the memory
  safe_free(db->memory);
  safe_free(db);
}

bv_domain_t* bv_feasible_set_db_get(bv_feasible_set_db_t* db, variable_t x) {
  uint32_t index = bv_feasible_set_db_get_index(db, x);

  // If no constraints, just return NULL
  if (index == 0) {
    return NULL;
  }

  bv_feasible_list_element_t* current = db->memory + index;
  return current->domain;
}

static
void bv_feasible_set_new_element(bv_feasible_set_db_t* db,
                                 variable_t x,
                                 bv_domain_t* domain,
                                 term_t* reason,
                                 bdds_t* reason_bdd) {
    
  // Allocate a new one
  uint32_t old_index = bv_feasible_set_db_get_index(db, x);
  uint32_t new_index = db->memory_size;
  // Allocate new element
  if (db->memory_size == db->memory_capacity) {
    db->memory_capacity = db->memory_capacity + db->memory_capacity/2;
    db->memory = safe_realloc(db->memory, db->memory_capacity*sizeof(bv_feasible_list_element_t));
  }
  db->memory_size ++;
  // Setup the element
  bv_feasible_list_element_t* new_element = db->memory + new_index;
  new_element->domain     = domain;
  new_element->reason     = reason;
  new_element->reason_bdd = reason_bdd;
  new_element->prev       = old_index;
  // Add to map
  int_hmap_pair_t* find = int_hmap_find(&db->var_to_eq_set_map, x);
  if (find == NULL) {
    int_hmap_add(&db->var_to_eq_set_map, x, new_index);
  } else {
    find->val = new_index;
  }
  // Add to updates list
  ivector_push(&db->updates, x);

  /* // If fixed, put into the fixed array */
  /* if (eq) { */
  /*   ivector_push(&db->fixed_variables, x); */
  /* } */
}

void bv_feasible_set_db_set_init(bv_feasible_set_db_t* db, variable_t x, uint32_t bitsize) {

  uint32_t index = bv_feasible_set_db_get_index(db, x);

  if (index != 0) assert(false);
  if (ctx_trace_enabled(db->ctx, "bv_plugin")) {
    ctx_trace_printf(db->ctx, "bv_feasible_set_db_init for variable ");
    variable_db_print_variable(db->ctx->var_db, x,ctx_trace_out(db->ctx));
    ctx_trace_printf(db->ctx, "\n");
  }

  bv_domain_t* domain = bv_domain_init(bitsize, x, db->manager, db->ctx);
  bv_feasible_set_new_element(db, x, domain, NULL, NULL);
}

bool bv_feasible_set_db_set_update(bv_feasible_set_db_t* db,
                                   variable_t x,
                                   term_t reason,
                                   const mcsat_value_t* v) {

  uint32_t index = bv_feasible_set_db_get_index(db, x);
  bv_feasible_list_element_t* current = db->memory + index;

  const varWnodes_t* varWnodes  = bv_domain_getvar(current->domain);
  bdds_t* reason_bdds     = bdds_create(1, varWnodes);
  bv_domain_t* new_domain = bv_domain_update(reason_bdds, reason, v, current->domain);

  // No new information, the BDD version of the reason is freed
  if (new_domain == current->domain) {
    bdds_clear(reason_bdds);
    bdds_free(reason_bdds);
    return false;
  }
  
  // Otherwise, new information, we record it
  bv_feasible_set_new_element(db, x, new_domain, &reason, reason_bdds);
  
  return false;
}


/* void bv_feasible_set_db_push(bv_feasible_set_db_t* db) { */
/*   scope_holder_push(&db->scope, */
/*      &db->updates.size, */
/*      &db->fixed_variables.size, */
/*      &db->fixed_variables_i, */
/*      NULL */
/*   ); */
/* } */

/* void bv_feasible_set_db_pop(bv_feasible_set_db_t* db) { */

/*   uint32_t old_updates_size; */
/*   uint32_t old_fixed_variable_size; */

/*   scope_holder_pop(&db->scope, */
/*       &old_updates_size, */
/*       &old_fixed_variable_size, */
/*       &db->fixed_variables_i, */
/*       NULL */
/*   ); */

/*   // Undo fixed variables */
/*   ivector_shrink(&db->fixed_variables, old_fixed_variable_size); */

/*   // Undo updates */
/*   while (db->updates.size > old_updates_size) { */
/*     // The variable that was updated */
/*     variable_t x = ivector_last(&db->updates); */
/*     ivector_pop(&db->updates); */
/*     // Remove the element */
/*     db->memory_size --; */
/*     bv_feasible_list_element_t* element = db->memory + db->memory_size; */
/*     uint32_t prev = element->prev; */
/*     // Redirect map to the previous one */
/*     int_hmap_pair_t* find = int_hmap_find(&db->var_to_eq_set_map, x); */
/*     assert(find != NULL); */
/*     assert(find->val == db->memory_size); */
/*     find->val = prev; */
/*   } */

/* } */

/* variable_t bv_feasible_set_db_get_eq_reason(bv_feasible_set_db_t* db, variable_t x) { */

/*   // Go back from the top reason for x and gather the indices */
/*   uint32_t index = bv_feasible_set_db_get_index(db, x); */
/*   assert(index); */

/*   assert(index); */
/*   while (index) { */
/*     bv_feasible_list_element_t* current = db->memory + index; */
/*     if (current->eq) { */
/*       return current->reason; */
/*     } */
/*     index = current->prev; */
/*   } */

/*   assert(false); */
/*   return variable_null; */
/* } */

/* void bv_feasible_set_db_get_conflict(bv_feasible_set_db_t* db, variable_t x, ivector_t* conflict) { */
/*   // Go back from the top reason for x and gather the indices */
/*   uint32_t index = bv_feasible_set_db_get_index(db, x); */
/*   assert(index); */

/*   // Conflict is always between top one and one some below */
/*   bv_feasible_list_element_t* first = db->memory + index; */

/*   bv_feasible_list_element_t* current = NULL; */

/*   index = first->prev; */
/*   assert(index); */
/*   while (index) { */

/*     current = db->memory + index; */

/*     if (first->eq && current->eq) { */
/*       // Second equality must be in conflict. */
/*       // We have x = y && x = z, implying different values on x */
/*       // Conflict is x = y && x = z && y != z */
/*       assert(first->value != current->value); */

/*       variable_t x_eq_y_var = first->reason; */
/*       variable_t x_eq_z_var = current->reason; */
/*       assert(trail_get_boolean_value(db->trail, x_eq_y_var)); */
/*       assert(trail_get_boolean_value(db->trail, x_eq_z_var)); */
/*       term_t x_eq_y = variable_db_get_term(db->var_db, x_eq_y_var); */
/*       term_t x_eq_z = variable_db_get_term(db->var_db, x_eq_z_var); */
/*       composite_term_t* x_eq_y_desc = eq_term_desc(db->terms, x_eq_y); */
/*       composite_term_t* x_eq_z_desc = eq_term_desc(db->terms, x_eq_z); */

/*       term_t x_term = variable_db_get_term(db->var_db, x); */
/*       term_t y_term = x_eq_y_desc->arg[0] == x_term ? x_eq_y_desc->arg[1] : x_eq_y_desc->arg[0]; */
/*       term_t z_term = x_eq_z_desc->arg[0] == x_term ? x_eq_z_desc->arg[1] : x_eq_z_desc->arg[0]; */
/*       term_t y_eq_z = yices_eq(y_term, z_term); */

/*       ivector_push(conflict, x_eq_y); */
/*       ivector_push(conflict, x_eq_z); */
/*       ivector_push(conflict, opposite_term(y_eq_z)); */

/*       return; */
/*     } */

/*     if (first->eq && !current->eq) { */
/*       if (first->value == current->value) { */
/*         // We have x = y && x != z, the conflict being */
/*         // x = y && x != z && y = z */

/*         variable_t x_eq_y_var = first->reason; */
/*         variable_t x_eq_z_var = current->reason; */
/*         assert(trail_get_boolean_value(db->trail, x_eq_y_var)); */
/*         assert(!trail_get_boolean_value(db->trail, x_eq_z_var)); */
/*         term_t x_eq_y = variable_db_get_term(db->var_db, x_eq_y_var); */
/*         term_t x_eq_z = variable_db_get_term(db->var_db, x_eq_z_var); */
/*         composite_term_t* x_eq_y_desc = eq_term_desc(db->terms, x_eq_y); */
/*         composite_term_t* x_eq_z_desc = eq_term_desc(db->terms, x_eq_z); */

/*         term_t x_term = variable_db_get_term(db->var_db, x); */
/*         term_t y_term = x_eq_y_desc->arg[0] == x_term ? x_eq_y_desc->arg[1] : x_eq_y_desc->arg[0]; */
/*         term_t z_term = x_eq_z_desc->arg[0] == x_term ? x_eq_z_desc->arg[1] : x_eq_z_desc->arg[0]; */
/*         term_t y_eq_z = yices_eq(y_term, z_term); */

/*         ivector_push(conflict, x_eq_y); */
/*         ivector_push(conflict, opposite_term(x_eq_z)); */
/*         ivector_push(conflict, y_eq_z); */

/*         return; */
/*       } */
/*     } */

/*     if (!first->eq && current->eq) { */
/*       // Equality: must be in conflict */
/*       assert(first->value == current->value); */

/*       // We have x != y && x = z, the conflict being */
/*       // x != y && x = z && y = z */

/*       variable_t x_eq_y_var = first->reason; */
/*       variable_t x_eq_z_var = current->reason; */
/*       assert(!trail_get_boolean_value(db->trail, x_eq_y_var)); */
/*       assert(trail_get_boolean_value(db->trail, x_eq_z_var)); */
/*       term_t x_eq_y = variable_db_get_term(db->var_db, x_eq_y_var); */
/*       term_t x_eq_z = variable_db_get_term(db->var_db, x_eq_z_var); */
/*       composite_term_t* x_eq_y_desc = eq_term_desc(db->terms, x_eq_y); */
/*       composite_term_t* x_eq_z_desc = eq_term_desc(db->terms, x_eq_z); */

/*       term_t x_term = variable_db_get_term(db->var_db, x); */
/*       term_t y_term = x_eq_y_desc->arg[0] == x_term ? x_eq_y_desc->arg[1] : x_eq_y_desc->arg[0]; */
/*       term_t z_term = x_eq_z_desc->arg[0] == x_term ? x_eq_z_desc->arg[1] : x_eq_z_desc->arg[0]; */
/*       term_t y_eq_z = yices_eq(y_term, z_term); */

/*       ivector_push(conflict, opposite_term(x_eq_y)); */
/*       ivector_push(conflict, x_eq_z); */
/*       ivector_push(conflict, y_eq_z); */

/*       return; */
/*     } */

/*     index = db->memory[index].prev; */
/*   } */

/*   assert(false); */
/* } */

/* void bv_feasible_set_db_gc_mark(bv_feasible_set_db_t* db, gc_info_t* gc_vars) { */

/*   assert(db->trail->decision_level == 0); */

/*   if (gc_vars->level == 0) { */
/*     // We keep all the reasons (start from 1, 0 is not used) */
/*     uint32_t element_i; */
/*     for (element_i = 1; element_i < db->memory_size; ++ element_i) { */
/*       bv_feasible_list_element_t* element = db->memory + element_i; */
/*       gc_info_mark(gc_vars, element->reason); */
/*     } */
/*   } */
/* } */

/* void bv_feasible_set_db_gc_sweep(bv_feasible_set_db_t* db, const gc_info_t* gc_vars) { */
/*   // We relocatre all reasons */
/*   uint32_t element_i; */
/*   for (element_i = 1; element_i < db->memory_size; ++ element_i) { */
/*     bv_feasible_list_element_t* element = db->memory + element_i; */
/*     variable_t x = element->reason; */
/*     x = gc_info_get_reloc(gc_vars, x); */
/*     assert(x != variable_null); */
/*     element->reason = x; */
/*   } */
/* } */



/* variable_t bv_feasible_set_db_get_fixed(bv_feasible_set_db_t* db) { */
/*   for (; db->fixed_variables_i < db->fixed_variables.size; ++ db->fixed_variables_i) { */
/*     variable_t var = db->fixed_variables.data[db->fixed_variables_i]; */
/*     if (!trail_has_value(db->trail, var)) { */
/*       return var; */
/*     } */
/*   } */
/*   return variable_null; */
/* } */
