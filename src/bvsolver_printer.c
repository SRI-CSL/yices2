/*
 * PRINT INTERNALS OF A BV_SOLVER
 */

#include <inttypes.h>

#include "bv64_constants.h"
#include "bv_constants.h"

#include "smt_core_printer.h"
#include "egraph_printer.h"
#include "bvsolver_printer.h"


/*
 * VARIABLE TABLE
 */
static void print_bvvar(FILE *f, thvar_t x) {
  fprintf(f, "u!%"PRId32, x);
}

static void print_bvvar_power(FILE *f, varexp_t *p) {
  print_bvvar(f, p->var);
  if (p->exp > 1) {
    fprintf(f, "^%"PRIu32, p->exp);
  }
}


static void print_bv_product(FILE *f, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  if (n == 0) {
    fprintf(f, "1");
  } else {
    i = 0;
    for (;;) {
      print_bvvar_power(f, p->prod + i);
      i ++;
      if (i == n) break;
      fputs(" * ", f);
    }
  }
}


// c = coeff, x = variable, n = number of bits
static void print_bv_mono64(FILE *f, uint64_t c, thvar_t x, uint32_t n, bool first) {
  if (c == 1) {    
    if (first) {
      if (x == const_idx) {
	fputs("1", f);
      } else {
	print_bvvar(f, x);
      }
    } else {
      fputs(" + ", f);
      print_bvvar(f, x);
    }

  } else if (bvconst64_is_minus_one(c, n)) {
    if (first) {
      if (x == const_idx) {
	fputs("-1", f);
      } else {
	fputs("- ", f);
	print_bvvar(f, x);
      }
    } else {
      fputs(" - ", f);
      print_bvvar(f, x);
    }

  } else {
    if (! first) {
      fputs(" + ", f);
    }

    bvconst64_print(f, c, n);
    if (x != const_idx) {
      fputs(" * ", f);
      print_bvvar(f, x);
    }
  }
}


static void print_bv_poly64(FILE *f, bvpoly64_t *p) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_bv_mono64(f, p->mono[i].coeff, p->mono[i].var, p->bitsize, first);
      first = false;
    }
  }
}



// monomial c * x: n = number of bits
static void print_bv_mono(FILE *f, uint32_t *c, thvar_t x, uint32_t n, bool first) {
  uint32_t w;

  w = (n + 31) >> 5; // number of words in c 
  if (bvconst_is_one(c, w)) {
    if (first) {
      if (x == const_idx) {
	fputs("1", f);
      } else {
	print_bvvar(f, x);
      }
    } else {
      fputs(" + ", f);
      print_bvvar(f, x);
    }

  } else if (bvconst_is_minus_one(c, n)) {
    if (first) {
      if (x == const_idx) {
	fputs("-1", f);
      } else {
	fputs("- ", f);
	print_bvvar(f, x);
      }
    } else {
      fputs(" - ", f);
      print_bvvar(f, x);
    }

  } else {
    if (! first) {
      fputs(" + ", f);
    }

    bvconst_print(f, c, n);
    if (x != const_idx) {
      fputs(" * ", f);
      print_bvvar(f, x);
    }
  }
}


static void print_bv_poly(FILE *f, bvpoly_t *p) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_bv_mono(f, p->mono[i].coeff, p->mono[i].var, p->bitsize, first);
      first = false;
    }
  }
}


static void print_bv_ite(FILE *f, bv_ite_t *ite) {
  fputs("(ite ", f);
  print_literal(f, ite->cond);
  fputc(' ', f);
  print_bvvar(f, ite->left);
  fputc(' ', f);
  print_bvvar(f, ite->right);
  fputc(')', f);
}


static void print_bv_binop(FILE *f, const char *op, thvar_t arg[2]) {
  fprintf(f, "(%s ", op);
  print_bvvar(f, arg[0]);
  fputc(' ', f);
  print_bvvar(f, arg[1]);
  fputc(')', f);
}


static void print_bvneg(FILE *f, thvar_t arg[2]) {
  fprintf(f, "(neg ");
  print_bvvar(f, arg[0]);
  fputc(')', f);
}


/*
 * Print the definition of x in vtbl
 */
static void print_bv_vardef(FILE *f, bv_vartable_t *vtbl, thvar_t x) {
  uint32_t nbits;

  assert(valid_bvvar(vtbl, x));

  nbits = bvvar_bitsize(vtbl, x);
  print_bvvar(f, x);
  fprintf(f, ":bv[%"PRIu32"] = ", nbits);
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_VAR:
    fputs("var", f);
    break;

  case BVTAG_CONST64:
    bvconst64_print(f, bvvar_val64(vtbl, x), nbits);
    break;

  case BVTAG_CONST:
    bvconst_print(f, bvvar_val(vtbl, x), nbits);
    break;

  case BVTAG_POLY64:
    print_bv_poly64(f, bvvar_poly64_def(vtbl, x));
    break;

  case BVTAG_POLY:
    print_bv_poly(f, bvvar_poly_def(vtbl, x));
    break;

  case BVTAG_PPROD:
    print_bv_product(f, bvvar_pprod_def(vtbl, x));
    break;

  case BVTAG_BIT_ARRAY:
    print_litarray(f, nbits, bvvar_bvarray_def(vtbl, x));
    break;

  case BVTAG_ITE:
    print_bv_ite(f, bvvar_ite_def(vtbl, x));
    break;

  case BVTAG_UDIV:
    print_bv_binop(f, "div", bvvar_binop(vtbl, x));
    break;

  case BVTAG_UREM:
    print_bv_binop(f, "rem", bvvar_binop(vtbl, x));
    break;
    
  case BVTAG_SDIV:
    print_bv_binop(f, "sdiv", bvvar_binop(vtbl, x));
    break;

  case BVTAG_SREM:
    print_bv_binop(f, "srem", bvvar_binop(vtbl, x));
    break;
    
  case BVTAG_SMOD:
    print_bv_binop(f, "smod", bvvar_binop(vtbl, x));
    break;

  case BVTAG_SHL:
    print_bv_binop(f, "shl", bvvar_binop(vtbl, x));
    break;

  case BVTAG_LSHR:
    print_bv_binop(f, "lshr", bvvar_binop(vtbl, x));
    break;
    
  case BVTAG_ASHR:
    print_bv_binop(f, "ashr", bvvar_binop(vtbl, x));
    break;

  case BVTAG_ADD:
    print_bv_binop(f, "add", bvvar_binop(vtbl, x));
    break;

  case BVTAG_SUB:
    print_bv_binop(f, "sub", bvvar_binop(vtbl, x));
    break;

  case BVTAG_MUL:
    print_bv_binop(f, "mul", bvvar_binop(vtbl, x));
    break;

  case BVTAG_NEG:
    print_bvneg(f, bvvar_binop(vtbl, x));
    break;
  }
}



/*
 * Pseudo literal s: print the literal mapped to s
 */
static void print_pseudo_literal(FILE *f, remap_table_t *table, literal_t s) {
  if (s != null_literal) {
    s = remap_table_find(table, s);
  }
  if (s == null_literal) {
    fputs("?", f);
  } else if (s == true_literal) {
    fputs("t", f);
  } else if (s == false_literal) {
    fputs("f", f);
  } else {
    if (is_neg(s)) fputc('~', f);
    fprintf(f, "p!%"PRId32, var_of(s));
  }
}


/*
 * Literal array a (of size n)
 */
static void print_pseudo_litarray(FILE *f, remap_table_t *remap, literal_t *a, uint32_t n) {
  uint32_t i;

  fputc('[', f);
  for (i=0; i<n; i++) {
    if (i > 0) fputc(' ', f);
    print_pseudo_literal(f, remap, a[i]);
  }
  fputc(']', f);
}



/*
 * All variables in vtbl
 */
void print_bv_vartable(FILE *f, bv_vartable_t *vtbl) {
  uint32_t i, n;

  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    print_bv_vardef(f, vtbl, i);
    fputc('\n', f);
  }
}




/*
 * Print the name of variable x
 */
void print_bv_solver_var(FILE *f, bv_solver_t *solver, thvar_t x) {
  print_bvvar(f, x);
}


/*
 * Print the definition of variable x
 */
void print_bv_solver_vardef(FILE *f, bv_solver_t *solver, thvar_t x) {
  print_bv_vardef(f, &solver->vtbl, x);
  fputc('\n', f);
}



/*
 * All variables in solver
 */
void print_bv_solver_vars(FILE *f, bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  literal_t *map;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    print_bv_vardef(f, vtbl, i);
    fputc('\n', f);
    map = bvvar_get_map(vtbl, i);
    if (map != NULL) {
      assert(solver->remap != NULL);
      fputs("             = ", f);
      print_pseudo_litarray(f, solver->remap, map, bvvar_bitsize(vtbl, i));
      fputc('\n', f);
    }
  }
}




/*
 * ATOMS
 */
static void print_atom_aux(FILE *f, const char *op, thvar_t left, thvar_t right) {
  fprintf(f, "(%s ", op);
  print_bvvar(f, left);
  fputc(' ', f);
  print_bvvar(f, right);
  fputc(')', f);
}

/*
 * Print atom
 */
static void print_bv_atom(FILE *f, bvatm_t *atm) {
  fputc('[', f);
  print_bvar(f, bvatm_bvar(atm));
  fputs(" := ", f);
  switch (bvatm_tag(atm)) {
  case BVEQ_ATM:
    print_atom_aux(f, "bveq", atm->left, atm->right);
    break;
  case BVUGE_ATM:
    print_atom_aux(f, "bvge", atm->left, atm->right);
    break;
  case BVSGE_ATM:    
    print_atom_aux(f, "bvsge", atm->left, atm->right);
    break;
  }
  fputc(']', f);
}



/*
 * All atoms in atbl
 */
void print_bv_atomtable(FILE *f, bv_atomtable_t *atbl) {
  uint32_t i, n;

  n = atbl->natoms;
  for (i=0; i<n; i++) {
    print_bv_atom(f, atbl->data + i);
    fputc('\n', f);
  }
}


void print_bv_solver_atoms(FILE *f, bv_solver_t *solver) {
  print_bv_atomtable(f, &solver->atbl);
}


/*
 * Atom i
 */
void print_bv_solver_atom(FILE *f, bv_solver_t *solver, int32_t id) {
  bv_atomtable_t *atbl;
  bvatm_t *atm;

  atbl = &solver->atbl;
  assert(0 <= id && id < atbl->natoms);

  atm = atbl->data + id;
  switch (bvatm_tag(atm)) {
  case BVEQ_ATM:
    print_atom_aux(f, "bveq", atm->left, atm->right);
    break;
  case BVUGE_ATM:
    print_atom_aux(f, "bvge", atm->left, atm->right);
    break;
  case BVSGE_ATM:    
    print_atom_aux(f, "bvsge", atm->left, atm->right);
    break;
  }

}


void print_bv_solver_atomdef(FILE *f, bv_solver_t *solver, int32_t id) {
  bv_atomtable_t *atbl;

  atbl = &solver->atbl;
  assert(0 <= id && id < atbl->natoms);
  print_bv_atom(f, atbl->data + id);
}


void print_bv_solver_atom_of_literal(FILE *f, bv_solver_t *solver, literal_t l) {
  void *atm;
  bvar_t v;
  int32_t id;

  v = var_of(l);
  assert(bvar_has_atom(solver->core, v));
  atm = bvar_atom(solver->core, v);
  assert(atom_tag(atm) == BV_ATM_TAG);
  id = bvatom_tagged_ptr2idx(atm);

  if (is_neg(l)) {
    fputs("(not ", f);
  }
  print_bv_solver_atom(f, solver, id);
  if (is_neg(l)) {
    fputc(')', f);
  }
}



/*
 * EXPANDED FORMS
 */

/*
 * Power product p
 */
static void print_bv_pprod(FILE *f, pprod_t *p) {
  assert(! pp_is_empty(p) && p != end_pp);
  if (pp_is_var(p)) {
    print_bvvar(f, var_of_pp(p));
  } else {
    print_bv_product(f, p);
  }
}


/*
 * Monomial coeff * r: 
 */
static void print_bvmlist64_mono(FILE *f, uint64_t coeff, pprod_t *r, uint32_t n, bool first) {
  if (pp_is_empty(r)) {
    if (!first) fprintf(f, " + ");
    bvconst64_print(f, coeff, n);
  } else if (coeff == 1) {
    if (!first) fprintf(f, " + ");
    print_bv_pprod(f, r);
  } else if (bvconst64_is_minus_one(coeff, n)) {
    if (!first) fprintf(f, " ");
    fprintf(f, "- ");
    print_bv_pprod(f, r);
  } else {
    if (!first) fprintf(f, " + ");
    bvconst64_print(f, coeff, n);
    fprintf(f, " ");
    print_bv_pprod(f, r);
  }
}

static void print_bvmlist_mono(FILE *f, uint32_t *coeff, pprod_t *r, uint32_t n, bool first) {
  uint32_t w;

  w = (n + 31) >> 5;

  if (pp_is_empty(r)) {
    if (!first) fprintf(f, " + ");
    bvconst_print(f, coeff, n);
  } else if (bvconst_is_one(coeff, w)) {
    if (!first) fprintf(f, " + ");
    print_bv_pprod(f, r);
  } else if (bvconst_is_minus_one(coeff, n)) {
    if (!first) fprintf(f, " ");
    fprintf(f, "- ");
    print_bv_pprod(f, r);
  } else {
    if (!first) fprintf(f, " + ");
    bvconst_print(f, coeff, n);
    fprintf(f, " ");
    print_bv_pprod(f, r);
  }
}


/*
 * List of monomials
 */
void print_bvexp64(FILE *f, bvmlist64_t *p, uint32_t n) {
  bool first;

  assert(p != NULL);

  if (p->next == NULL) {
    fprintf(f, "0");
  } else {
    first = true;
    while (p->next != NULL) {
      print_bvmlist64_mono(f, p->coeff, p->prod, n, first);
      first = false;
      p = p->next;
    }
  }
}

void print_bvexp(FILE *f, bvmlist_t *p, uint32_t n) {
  bool first;

  assert(p != NULL);

  if (p->next == NULL) {
    fprintf(f, "0");
  } else {
    first = true;
    while (p->next != NULL) {
      print_bvmlist_mono(f, p->coeff, p->prod, n, first);
      first = false;
      p = p->next;
    }
  }    
}



/*
 * VARIABLE SUBSTITUTIONS
 */
void print_bv_solver_partition(FILE *f, bv_solver_t *solver) {
  mtbl_t *mtbl;
  uint32_t i, n;
  thvar_t x;

  mtbl = &solver->mtbl;
  n = mtbl->top;
  for (i=0; i<n; i++) {
    x = mtbl_get_root(mtbl, i);
    if (x != i) {
      print_bvvar(f, i);
      fputs(" --> ", f);
      print_bvvar(f, x);
      fputc('\n', f);
    }
  }
}




/*
 * BOUNDS IN THE SOLVER QUEUE
 */

/*
 * Bound in the given descriptor
 */
static void print_bv_solver_bound(FILE *f, bv_solver_t *solver, bv_bound_t *b) {
  bvatm_t *atm;
  bvar_t x;

  atm = bvatom_desc(&solver->atbl, b->atom_id);
  switch (bvatm_tag(atm)) {
  case BVEQ_ATM:
    print_atom_aux(f, "bveq", atm->left, atm->right);
    break;
  case BVUGE_ATM:
    print_atom_aux(f, "bvge", atm->left, atm->right);
    break;
  case BVSGE_ATM:    
    print_atom_aux(f, "bvsge", atm->left, atm->right);
    break;
  }

  fputs(" --> ", f);
  x = bvatm_bvar(atm);
  print_bval(f, bvar_base_value(solver->core, x));
}


void print_bv_solver_bounds(FILE *f, bv_solver_t *solver) {
  bv_bound_queue_t *queue;
  uint32_t i, n;

  queue = &solver->bqueue;
  n = queue->top;
  for (i=0; i<n; i++) {
    fprintf(f, " bound[%"PRIu32"]: ", i);
    print_bv_solver_bound(f, solver, queue->data + i);
    fputc('\n', f);
  }
}
