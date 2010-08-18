/*
 * PRINTER FOR THE RDL FLOYD-WARSHALL SOLVER
 */

#include <inttypes.h>

#include "rationals.h"
#include "smt_core_printer.h"
#include "rdl_fw_printer.h"


/*
 * Print rdl variable x
 */
void print_rdl_var(FILE *f, int32_t x) {
  if (x >= 0) {
    fprintf(f, "x!%"PRId32, x);
  } else if (x == null_rdl_vertex) {
    fputs("null", f);
  } else {
    fprintf(f, "RDLV%"PRId32, x);
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
 * Print atom
 */
void print_rdl_atom(FILE *f, rdl_atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := (", f);
  print_rdl_var(f, atom->source);
  fputs(" - ", f);
  print_rdl_var(f, atom->target);
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
 * Value of var v in the rdl solver
 *
 * HACK:
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
void print_rdl_var_value(FILE *f, rdl_solver_t *rdl, int32_t v) {
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



