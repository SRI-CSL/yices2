/*
 * PRINTER FOR THE IDL FLOYD-WARSHALL SOLVER
 */

#include <inttypes.h>

#include "smt_core_printer.h"
#include "idl_fw_printer.h"


/*
 * Print vertex x
 */
void print_idl_vertex(FILE *f, int32_t x) {
  if (x >= 0) {
    fprintf(f, "n!%"PRId32, x);
  } else if (x == null_idl_vertex) {
    fputs("nil", f);
  } else {
    fprintf(f, "<IDL-vertex%"PRId32">", x);
  }
}


/*
 * Value of vertex v in the idl solver
 *
 * HACK:
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
void print_idl_vertex_value(FILE *f, idl_solver_t *idl, int32_t v) {
  idl_matrix_t *m;
  idl_cell_t *cell;
  int32_t z;

  m = &idl->graph.matrix;
  z = idl->zero_vertex;
  if (z == null_idl_vertex) {
    z = 0;
  }
  
  if (m != NULL && z < m->dim && v < m->dim) {
    cell = m->data + z * m->dim + v;
    if (cell->id >= 0) {
      // distance [z, x] is defined
      fprintf(f, "%"PRId32, cell->dist);
      return;
    }
  }

  fprintf(f, "???");
}


/*
 * Print atom
 */
void print_idl_atom(FILE *f, idl_atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := (", f);
  print_idl_vertex(f, atom->source);
  fputs(" - ", f);
  print_idl_vertex(f, atom->target);
  fprintf(f, " <= %3"PRId32")]", atom->cost);
}


/*
 * Print all atoms in idl solver
 */
void print_idl_atoms(FILE *f, idl_solver_t *idl) {
  uint32_t i, n;

  n = idl->atoms.natoms;
  for (i=0; i<n; i++) {
    print_idl_atom(f, idl->atoms.atoms + i);
    fputc('\n', f);
  }
}



/*
 * Difference logic triple (x - y + d)
 * - x and y are vertices
 */
void print_idl_triple(FILE *f, dl_triple_t *triple) {
  bool space;

  space = false;
  if (triple->target >= 0) {
    print_idl_vertex(f, triple->target); // x
    space = true;
  }
  if (triple->source >= 0) {
    if (space) fputc(' ', f);
    fputs("- ", f);
    print_idl_vertex(f, triple->source); // y
  }


  if (! space) {
    q_print(f, &triple->constant); 
  } else if (q_is_pos(&triple->constant)) {
    printf(" + ");
    q_print(f, &triple->constant);
  } else if (q_is_neg(&triple->constant)) {
    printf(" - ");
    q_print_abs(f, &triple->constant);
  }
}



/*
 * Variable name
 */
void print_idl_var_name(FILE *f, thvar_t u) {
  if (u >= 0) {
    fprintf(f, "i!%"PRId32, u);
  } else if (u == null_thvar) {
    fputs("nil-var", f);
  } else {
    fprintf(f, "<IDL-var%"PRId32">", u);
  }
} 


/*
 * Print u + its descriptor
 */
void print_idl_var_def(FILE *f, idl_solver_t *solver, thvar_t u) {
  dl_vartable_t *vtbl;

  vtbl = &solver->vtbl;
  print_idl_var_name(f, u);
  if (0 <= u && u < vtbl->nvars) {
    fputs(" := ", f);
    print_idl_triple(f, dl_var_triple(vtbl, u));
  } else {
    fputs(" ???", f);
  }
}


/*
 * Print the full variable table
 */
void print_idl_var_table(FILE *f, idl_solver_t *solver) {
  uint32_t i, n;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    print_idl_var_def(f, solver, i);
    fputc('\n', f);
  }
}
