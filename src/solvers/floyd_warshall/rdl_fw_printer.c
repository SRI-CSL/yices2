/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINTER FOR THE RDL FLOYD-WARSHALL SOLVER
 */

#include <inttypes.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/floyd_warshall/rdl_fw_printer.h"
#include "terms/rationals.h"


/*
 * Print vertex x
 */
void print_rdl_vertex(FILE *f, int32_t x) {
  if (x >= 0) {
    fprintf(f, "v!%"PRId32, x);
  } else if (x == null_rdl_vertex) {
    fputs("nil", f);
  } else {
    fprintf(f, "<RDL-vertex%"PRId32">", x);
  }
}

/*
 * Constant used by rdl solver = rational + k * delta
 */
void print_rdl_const(FILE *f, rdl_const_t *c) {
  int32_t d;

  d = c->delta;

  if (q_is_zero(&c->q)) {
    if (d == 0) {
      fputc('0', f);
    } else {
      if (d < 0) {
        fputs("- ", f);
        d = - d;
      }
      if (d == 1) {
        fputs("delta", f);
      } else {
        fprintf(f, "%"PRId32" * delta", d);
      }
    }
  } else {
    q_print(f, &c->q);
    if (d != 0) {
      if (d < 0) {
        fputs(" - ", f);
        d = - d;
      } else {
        fputs(" + ", f);
      }
      if (d == 1) {
        fputs("delta", f);
      } else {
        fprintf(f, "%"PRId32" * delta", d);
      }
    }
  }
}




/*
 * Value of vertex x in the rdl solver
 *
 * HACK:
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
void print_rdl_vertex_value(FILE *f, rdl_solver_t *rdl, int32_t v) {
  rdl_matrix_t *m;
  rdl_cell_t *cell;
  int32_t z;

  m = &rdl->graph.matrix;
  z = rdl->zero_vertex;
  if (z == null_rdl_vertex) z = 0;

  if (m != NULL && z < m->dim && v < m->dim) {
    cell = m->data + z * m->dim + v;
    if (cell->id >= 0) {
      // distance [z, x] is defined
      print_rdl_const(f, &cell->dist);
      return;
    }
  }

  fprintf(f, "???");
}




/*
 * Print atom
 */
void print_rdl_atom(FILE *f, rdl_atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := (", f);
  print_rdl_vertex(f, atom->source);
  fputs(" - ", f);
  print_rdl_vertex(f, atom->target);
  fprintf(f, " <= ");
  q_print(f, &atom->cost);
  fprintf(f, ")]");
}


/*
 * Print all atoms in rdl solver
 */
void print_rdl_atoms(FILE *f, rdl_solver_t *rdl) {
  uint32_t i, n;

  n = rdl->atoms.natoms;
  for (i=0; i<n; i++) {
    print_rdl_atom(f, rdl->atoms.atoms + i);
    fputc('\n', f);
  }
}


/*
 * Difference logic triple (x - y + d)
 * - x and y are vertices
 */
void print_rdl_triple(FILE *f, dl_triple_t *triple) {
  bool space;

  space = false;
  if (triple->target >= 0) {
    print_rdl_vertex(f, triple->target); // x
    space = true;
  }
  if (triple->source >= 0) {
    if (space) fputc(' ', f);
    fputs("- ", f);
    print_rdl_vertex(f, triple->source); // y
    space = true;
  }

  if (! space) {
    q_print(f, &triple->constant);
  } else if (q_is_pos(&triple->constant)) {
    fprintf(f, " + ");
    q_print(f, &triple->constant);
  } else if (q_is_neg(&triple->constant)) {
    fprintf(f, " - ");
    q_print_abs(f, &triple->constant);
  }
}



/*
 * Variable name
 */
void print_rdl_var_name(FILE *f, thvar_t u) {
  if (u >= 0) {
    fprintf(f, "x!%"PRId32, u);
  } else if (u == null_thvar) {
    fputs("nil-var", f);
  } else {
    fprintf(f, "<RDL-var%"PRId32">", u);
  }
}


/*
 * Print u + its descriptor
 */
void print_rdl_var_def(FILE *f, rdl_solver_t *solver, thvar_t u) {
  dl_vartable_t *vtbl;

  vtbl = &solver->vtbl;
  print_rdl_var_name(f, u);
  if (0 <= u && u < vtbl->nvars) {
    fputs(" := ", f);
    print_rdl_triple(f, dl_var_triple(vtbl, u));
  } else {
    fputs(" ???", f);
  }
}


/*
 * Print the full variable table
 */
void print_rdl_var_table(FILE *f, rdl_solver_t *solver) {
  uint32_t i, n;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    print_rdl_var_def(f, solver, i);
    fputc('\n', f);
  }
}




/*
 * Cell x, y
 */
static inline rdl_cell_t *rdl_cell(rdl_matrix_t *m, uint32_t x, uint32_t y) {
  assert(0 <= x && x < m->dim && 0 <= y && y < m->dim);
  return m->data + x * m->dim + y;
}

/*
 * Distance from x to y
 */
static inline rdl_const_t *rdl_dist(rdl_matrix_t *m, uint32_t x, uint32_t y) {
  assert(rdl_cell(m, x, y)->id >= 0);
  return &rdl_cell(m, x, y)->dist;
}



/*
 * Print edge i
 */
static void print_rdl_edge(FILE *f, rdl_solver_t *solver, uint32_t i) {
  rdl_matrix_t *m;
  rdl_edge_t *e;
  rdl_const_t *d;
  thvar_t x, y;

  assert(0 < i && i < solver->graph.edges.top);
  e = solver->graph.edges.data + i;
  m = &solver->graph.matrix;

  x = e->source;
  y = e->target;
  d = rdl_dist(m, x, y);

  fprintf(f, "edge[%"PRIu32"]: v!%"PRId32" - v!%"PRId32" <= ", i, x, y);
  print_rdl_const(f, d);
}


/*
 * Print all edges
 */
void print_rdl_edges(FILE *f, rdl_solver_t *solver) {
  uint32_t i, n;

  n = solver->graph.edges.top;
  for (i=1; i<n; i++) {
    print_rdl_edge(f, solver, i);
    fputc('\n', f);
  }
}



/*
 * All axioms: edges labeled with true_literal
 */
void print_rdl_axioms(FILE *f, rdl_solver_t *solver) {
  uint32_t i, n;

  n = solver->graph.edges.top;
  for (i=1; i<n; i++) {
    if (solver->graph.edges.lit[i] == true_literal) {
      print_rdl_edge(f, solver, i);
      fputc('\n', f);
    }
  }
}
