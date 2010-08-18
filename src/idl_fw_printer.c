/*
 * PRINTER FOR THE IDL FLOYD-WARSHALL SOLVER
 */

#include <inttypes.h>

#include "smt_core_printer.h"
#include "idl_fw_printer.h"


/*
 * Print idl variable x
 */
void print_idl_var(FILE *f, int32_t x) {
  if (x >= 0) {
    fprintf(f, "y!%"PRId32, x);
  } else if (x == null_idl_vertex) {
    fputs("null", f);
  } else {
    fprintf(f, "IDLV%"PRId32, x);
  }
}

/*
 * Print atom
 */
void print_idl_atom(FILE *f, idl_atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := (", f);
  print_idl_var(f, atom->source);
  fputs(" - ", f);
  print_idl_var(f, atom->target);
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
 * Value of var v in the idl solver
 *
 * HACK:
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
void print_idl_var_value(FILE *f, idl_solver_t *idl, int32_t v) {
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


