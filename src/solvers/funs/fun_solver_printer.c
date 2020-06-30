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
 * PRINT FUNCTION/ARRAY SOLVER STRUCTURES
 */

#include <inttypes.h>

#include "io/type_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/funs/fun_solver_printer.h"
#include "utils/pointer_vectors.h"



/*
 * Print edge i
 */
void print_fsolver_edge(FILE *f, fun_solver_t *solver, uint32_t edge_id) {
  fun_edgetable_t *etbl;
  fun_edge_t *e;
  uint32_t i, n;

  etbl = &solver->etbl;
  assert(0 <= edge_id && edge_id < etbl->nedges);
  e = etbl->data[edge_id];

  fprintf(f, "edge[%"PRIu32"] : f!%"PRIu32" ---> f!%"PRIu32" [", edge_id, e->source, e->target);
  n = solver->vtbl.arity[e->source];
  assert(solver->vtbl.arity[e->target] == n);
  for (i=0; i<n; i++) {
    if (i>0) {
      fputc(' ', f);
    }
    print_occurrence(f, e->index[i]);
  }
  fprintf(f, "]");
}


/*
 * Print the edges
 */
void print_fsolver_edges(FILE *f, fun_solver_t *solver) {
  uint32_t i, n;

  n = solver->etbl.nedges;
  for (i=0; i<n; i++) {
    print_fsolver_edge(f, solver, i);
    fputc('\n', f);
  }
  fflush(f);
}


/*
 * Print the variables
 */
void print_fsolver_vars(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    fprintf(f, "var f!%"PRId32": eterm = ", i);
    print_eterm_id(f, vtbl->eterm[i]);
    if (tst_bit(vtbl->fdom, i)) {
      fprintf(f, ", finite domain");
    }
    fprintf(f, ", type: ");
    print_type_def(f, solver->types, vtbl->type[i]);
    fprintf(f, "\n");
  }
  fflush(f);
}


/*
 * Print the root variables
 */
void print_fsolver_roots(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    fprintf(f, "root[f!%"PRIu32"] = f!%"PRIu32", eterm[f!%"PRIu32"] = ", i, vtbl->root[i], i);
    print_eterm_id(f, vtbl->eterm[i]);
    fputc('\n', f);
  }
  fflush(f);
}


/*
 * Print the equivalence classes
 */
void print_fsolver_classes(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      // i is a root:
      fprintf(f, "class of f!%"PRIu32" = {", i);
      x = i;
      do {
        fprintf(f, " f!%"PRId32, x);
        x = vtbl->next[x];
      } while (x != null_thvar);
      fprintf(f, " }\n");
    }
  }
}


/*
 * Print the application vectors
 */
void print_fsolver_apps(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  composite_t **p;
  uint32_t i, n, j, m;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      p = (composite_t **) vtbl->app[i];
      if (p != NULL) {
        fprintf(f, "--- Apps for f!%"PRIu32" ---\n", i);
        m = pv_size((void **) p);
        for (j=0; j<m; j++) {
          print_composite(f, p[j]);
          fputs("  == ", f);
          print_label(f, egraph_term_label(solver->egraph, p[j]->id));
          fputc('\n', f);
        }
      } else {
        fprintf(f, "--- No apps for f!%"PRIu32" ---\n", i);
      }
    }
  }
  fflush(f);
}



/*
 * Print (f i_1 ... i_n) as a map element
 */
static void print_map(FILE *f, egraph_t *egraph, composite_t *c) {
  uint32_t i, n;

  assert(composite_kind(c) == COMPOSITE_APPLY);

  n = composite_arity(c);
  fputc('[', f);
  for (i=1; i<n; i++) {
    print_label(f, egraph_label(egraph, composite_child(c, i)));
    fputc(' ', f);
  }
  fputs("|-> ", f);
  print_label(f, egraph_term_label(egraph, c->id));
  fputs("]\n", f);
}


/*
 * Print the application vectors + base labels
 * - formatted as a mapping form egraph labels to egraph labels
 */
void print_fsolver_maps(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  egraph_t *egraph;
  composite_t **p;
  uint32_t i, n, j, m;

  egraph = solver->egraph;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      fprintf(f, "--- Map for f!%"PRIu32" ---\n", i);
      fprintf(f, "base = %"PRId32"\n", vtbl->base[i]);
      p = (composite_t **) vtbl->app[i];
      if (p != NULL) {
        m = pv_size((void **) p);
        for (j=0; j<m; j++) {
          print_map(f, egraph, p[j]);
        }
      }
    }
  }

}


/*
 * Print the base values for every root variable
 */
void print_fsolver_base_values(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;
  int32_t c, k;

  if (solver->base_value == NULL) {
    fputs("no base values\n", f);
    return;
  }

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      c = vtbl->base[i];
      k = solver->base_value[c];
      fprintf(f, "base value for f!%"PRIu32": ", i);
      if (k < 0) {
        fprintf(f, "fresh(%"PRId32")\n", - (k + 1));
      } else if (k == INT32_MAX) {
        fputs("unknown\n", f);
      } else {
        print_label(f, k);
        fputc('\n', f);
      }
    }
  }
}



/*
 * Print particle x as an index
 */
static void print_particle_index(FILE *f, egraph_t *egraph, particle_t x) {
  pstore_t *store;
  particle_tuple_t *tup;
  uint32_t i, n;

  store = egraph->mdl.pstore;
  switch (particle_kind(store, x)) {
  case LABEL_PARTICLE:
    print_label(f, particle_label(store, x));
    break;
  case FRESH_PARTICLE:
    fprintf(f, "fresh!%"PRId32, x);
    break;
  case TUPLE_PARTICLE:
    tup = tuple_particle_desc(store, x);
    n = tup->nelems;
    for (i=0; i<n; i++) {
      if (i>0) fputc(' ', f);
      print_particle_index(f, egraph, tup->elem[i]);
    }
    break;
  }
}

/*
 * Print particle x as a value
 */
static void print_particle_value(FILE *f, egraph_t *egraph, particle_t x) {
  pstore_t *store;
  particle_tuple_t *tup;
  uint32_t i, n;

  store = egraph->mdl.pstore;
  switch (particle_kind(store, x)) {
  case LABEL_PARTICLE:
    print_label(f, particle_label(store, x));
    break;
  case FRESH_PARTICLE:
    fprintf(f, "fresh!%"PRId32, x);
    break;
  case TUPLE_PARTICLE:
    tup = tuple_particle_desc(store, x);
    n = tup->nelems;
    fputs("(tuple", f);
    for (i=0; i<n; i++) {
      fputc(' ', f);
      print_particle_value(f, egraph, tup->elem[i]);
    }
    fputc(')', f);
    break;
  }
}

/*
 * Print the mapping [idx -> value]
 */
static void print_map_elem(FILE *f, egraph_t *egraph, particle_t idx, particle_t val) {
  fputc('[', f);
  print_particle_index(f, egraph, idx);
  fputs(" -> ", f);
  print_particle_value(f, egraph, val);
  fputs("]\n", f);
}


/*
 * Print the values
 */
void print_fsolver_values(FILE *f, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  egraph_t *egraph;
  map_t *map;
  uint32_t i, n, j;

  egraph = solver->egraph;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      fprintf(f, "--- Value for f!%"PRIu32" ---\n", i);
      map = solver->value[i];
      if (map != NULL) {
        for (j=0; j<map->nelems; j++) {
          print_map_elem(f, egraph, map->data[j].index, map->data[j].value);
        }
        if (map->def != null_particle) {
          fputs("[else -> ", f);
          print_particle_value(f, egraph, map->def);
          fputs("]\n", f);
        }
      }
    }
  }

}


/*
 * Print the asserted disequalities
 */
void print_fsolver_diseqs(FILE *f, fun_solver_t *solver) {
  diseq_stack_t *dstack;
  uint32_t i, n;

  dstack = &solver->dstack;
  n = dstack->top;
  for (i=0; i<n; i++) {
    fprintf(f, "diseq[%"PRIu32"]: f!%"PRIu32" != f%"PRIu32"\n", i, dstack->data[i].left, dstack->data[i].right);
  }

}


/*
 * Print stratification structure
 */
void print_fsolver_stratification(FILE *f, stratification_t *s, fun_solver_t *solver) {
  diseq_stack_t *dstack;
  uint32_t i, j, k, n, m, d;

  i = 0;
  n = strat_num_levels(s);
  for (k=0; k<n; k++) {
    m = num_vars_in_stratum(s, k);
    for (j=0; j<m; j++) {
      fprintf(f, "f!%"PRId32": level = %"PRIu32"\n", s->vars[i], k);
      i ++;
    }
  }
  fprintf(f, "\n");
  
  dstack = &solver->dstack;
  i = 0;
  for (k=0; k<n; k++) {
    m = num_diseqs_in_stratum(s, k);
    for (j=0; j<m; j++) {
      d = s->diseqs[i];
      fprintf(f, "diseq[%"PRIu32"]: level = %"PRIu32": f!%"PRId32" != f!%"PRId32"\n",
	      d, k, dstack->data[d].left, dstack->data[d].right);
      i ++;
    }
  }
  fprintf(f, "\n");
}
