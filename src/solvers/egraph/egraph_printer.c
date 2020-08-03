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
 * PRINT EGRAPH STRUCTURES
 */

#include <inttypes.h>

#include "io/type_printer.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/egraph/egraph_utils.h"
#include "solvers/egraph/theory_explanations.h"
#include "utils/int_array_sort.h"
#include "utils/int_hash_sets.h"
#include "utils/prng.h"
#include "utils/ptr_vectors.h"



/****************
 *  NAME TABLE  *
 ***************/

/*
 * The name table can be setup for a single context, after internalization.
 * The table keeps track of the mappings from solver objects to the name
 * of the corresponding term in the global term table.
 */
static uint32_t name_size = 0;
static char **name = NULL;


static const char * const etype2string[] = {
  "int ", "real", "bv  ", "quant ", "fun ", "bool", "tupl", "none", "<invalid etype>",
};

static const char * const etype2theory[] = {
  "arith", "arith", "bv", "quant", "fun", "bool", "tuple", "none", "<invalid etype>",
};

static const char * const cmpkind2string[] = {
  "apply", "update", "tuple", "eq", "ite", "distinct", "or", "lambda", "<invalid composite kind>",
};



/*
 * Basic egraph objects
 */
void print_etype(FILE *f, etype_t tau) {
  // the cast to (int) prevents annoying warnings
  // when compiling with Clang
  if ((int) tau < 0 || tau > NUM_ETYPES) {
    tau = NUM_ETYPES;
  }
  fputs(etype2string[tau], f);
}


/*
 * Theory name for type tau
 */
void print_theory_id(FILE *f, etype_t tau) {
  // the cast to (int) prevents annoying warnings
  // when compiling with Clang
  if ((int) tau < 0 || tau > NUM_ETYPES) {
    tau = NUM_ETYPES;
  }
  fputs(etype2theory[tau], f);
}


/*
 * Term id
 */
static void print_eterm_name(FILE *f, eterm_t t) {
  assert(t >= 0);
  if (t < name_size && name[t] != NULL) {
    fputs(name[t], f);
  } else {
    fprintf(f, "g!%"PRId32, t);
  }
}

void print_eterm_id(FILE *f, eterm_t t) {
  if (t <= 0) {
    if (t == null_eterm) {
      fputs("null_eterm", f);
    } else if (t == true_eterm) {
      fputs("tt", f);
    } else {
      fprintf(f, "ETERM%"PRId32, t);
    }
  } else {
    print_eterm_name(f, t);
  }
}

/*
 * Theory variable
 */
void print_thvar(FILE *f, thvar_t v) {
  if (v < 0) {
    if (v == null_thvar) {
      fputs("null_thvar", f);
    } else {
      fprintf(f, "THVAR%"PRId32, v);
    }
  } else {
    fprintf(f, "v!%"PRId32, v);
  }
}


/*
 * Term id + polarity
 */
void print_occurrence(FILE *f, occ_t t) {
  if (t < 0) {
    if (t == null_occurrence) {
      fputs("null", f);
    } else {
      fprintf(f, "OCC%"PRId32, t);
    }
  } else if (t == true_occ) {
    fputs("tt", f);
  } else if (t == false_occ) {
    fputs("ff", f);
  } else {
    if (is_neg_occ(t)) fputc('~', f);
    print_eterm_name(f, term_of_occ(t));
  }
}

/*
 * Class id
 */
void print_class_id(FILE *f, class_t c) {
  if (c < 0) {
    if (c == null_class) {
      fputs("null_class", f);
    } else {
      fprintf(f, "CLASS%"PRId32, c);
    }
  } else {
    fprintf(f, "C!%"PRId32, c);
  }
}

/*
 * Label: class id + polarity
 */
void print_label(FILE *f, elabel_t l) {
  char sgn;

  if (l < 0) {
    if (l == null_label) {
      fputs("null_label", f);
    } else {
      fprintf(f, "LABEL%"PRId32, l);
    }
  } else {
    fprintf(f, "C!%"PRId32, class_of(l));
    sgn = is_pos_label(l) ? '+' : '-';
    fputc(sgn, f);
  }
}


/*
 * Dmask: bit vector
 */
void print_dmask(FILE *f, uint32_t d) {
  uint32_t k, m;
  char bit;

  m = ((uint32_t) 1) << 31;
  for (k=0; k<32; k++) {
    bit = '0';
    if ((d & m) != 0) bit = '1';
    fputc(bit, f);
    m >>= 1;
  }
}


/*
 * EGRAPH: INTERNAL STATE
 */
static void print_kind(FILE *f, composite_kind_t k) {
  // cast to (int) to prevent compilation warnings with clang
  if ((int) k < 0 || k > COMPOSITE_LAMBDA) {
    k = COMPOSITE_LAMBDA + 1;
  }
  fputs(cmpkind2string[k], f);
}

void print_composite(FILE *f, composite_t *c) {
  uint32_t i, n;
  composite_kind_t k;

  k = composite_kind(c);
  n = composite_arity(c);

  fputc('(', f);
  switch (k) {
  case COMPOSITE_APPLY:
    print_occurrence(f, c->child[0]);
    for (i=1; i<n; i++) {
      fputc(' ', f);
      print_occurrence(f, c->child[i]);
    }
    break;

  case COMPOSITE_LAMBDA:
    print_kind(f, COMPOSITE_LAMBDA);
    fprintf(f, "[%"PRId32"] ", c->child[2]); // print the lambda tag
    print_occurrence(f, c->child[0]);
    break;

  default:
    print_kind(f, composite_kind(c));
    for (i=0; i<n; i++) {
      fputc(' ', f);
      print_occurrence(f, c->child[i]);
    }
    break;
  }

  fputc(')', f);
}

void print_signature(FILE *f, signature_t *s) {
  uint32_t i, n;

  n = tag_arity(s->tag);
  fputc('[', f);
  print_kind(f, tag_kind(s->tag));
  if (tag_kind(s->tag) == COMPOSITE_LAMBDA) {
    fprintf(f, "[%"PRId32"]", s->sigma[1]); // print the lambda tag
  }
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_label(f, s->sigma[i]);
  }
  fputc(']', f);
}





/*
 * Parent vectors: skip all non-valid entries
 */
void print_parents(FILE *f, use_vector_t *v) {
  uint32_t i, n;
  composite_t *p;

  n = v->last;
  for (i=0; i<n; i++) {
    p = v->data[i];
    if (valid_entry(p)) {
      fputs("  ", f);
      print_composite(f, p);
      fputc('\n', f);
    }
  }
}


void print_parents_details(FILE *f, use_vector_t *v) {
  uint32_t i, n;
  composite_t *p;

  n = v->last;
  for (i=0; i<n; i++) {
    p = v->data[i];
    if (valid_entry(p)) {
      fputs("  ", f);
      print_composite(f, p);
      fputc('\n', f);
    } else if (marked_entry(p)) {
      fputs("  ", f);
      print_composite(f, unmark_entry(p));
      fputs(" [hidden]\n", f);
    }
  }
}


/*
 * Print a theory explanation
 */
void print_th_eq(FILE *f, th_eq_t *eq) {
  fputc('(', f);
  print_eterm_id(f, eq->lhs);
  fputs(" = ", f);
  print_eterm_id(f, eq->rhs);
  fputc(')', f);
}

void print_th_diseq(FILE *f, diseq_pre_expl_t *diseq) {
  fputc('(', f);
  print_eterm_id(f, diseq->t1);
  fputs(" != ", f);
  print_eterm_id(f, diseq->t2);
  fputc(')', f);
}

static void print_literal_array(FILE *f, literal_t *a, uint32_t n) {
  uint32_t i;

  assert(n > 0);
  i = 0;
  for (;;) {
    print_literal(f, a[i]);
    i ++;
    if (i >= n) break;
    fputc(' ', f);
  }
}



static void print_th_eq_array(FILE *f, th_eq_t *a, uint32_t n) {
  uint32_t i;

  assert(n > 0);
  i = 0;
  for (;;) {
    print_th_eq(f, a + i);
    i ++;
    if (i >= n) break;
    fputc(' ', f);
  }
}

static void print_th_diseq_array(FILE *f, diseq_pre_expl_t *a, uint32_t n) {
  uint32_t i;

  assert(n > 0);
  i = 0;
  for (;;) {
    print_th_diseq(f, a + i);
    i ++;
    if (i >= n) break;
    fputc(' ', f);
  }
}

void print_theory_explanation(FILE *f, th_explanation_t *e) {
  literal_t *atoms;
  th_eq_t *eqs;
  diseq_pre_expl_t *diseqs;
  bool empty;

  empty = true;

  atoms = e->atoms;
  if (atoms != NULL && get_av_size(atoms) > 0) {
    print_literal_array(f, atoms, get_av_size(atoms));
    empty = false;
  }

  eqs = e->eqs;
  if (eqs != NULL && get_eqv_size(eqs) > 0) {
    if (! empty) fputc('\n', f);
    print_th_eq_array(f, eqs, get_eqv_size(eqs));
    empty = false;
  }

  diseqs = e->diseqs;
  if (diseqs != NULL && get_diseqv_size(diseqs) > 0) {
    if (! empty) fputc('\n', f);
    print_th_diseq_array(f, diseqs, get_diseqv_size(diseqs));
    empty = false;
  }

  if (empty) {
    fputs("<empty explanation>", f);
  }
  fflush(f);
}


void print_egraph_conflict(FILE *f, egraph_t *egraph, ivector_t *expl_vector) {
  void *atom;
  uint32_t i, n;
  literal_t l;
  bvar_t v;

  n = expl_vector->size;
  for (i=0; i<n; i++) {
    l = expl_vector->data[i];
    v = var_of(l);
    if (bvar_has_atom(egraph->core, v)) {
      atom = bvar_atom(egraph->core, v);
      switch (atom_tag(atom)) {
      case EGRAPH_ATM_TAG:
	if (is_neg(l)) fputs("(not ", f);
	print_eterm(f, egraph, ((atom_t *) untag_atom(atom))->eterm);
	if (is_neg(l)) fputc(')', f);
	break;

      default:
	print_literal(f, l);
	break;
      }
    } else {
      print_literal(f, l);
    }
    if (i+1 < n) {
      fputc(' ', f);
    }
  }
  fflush(f);
}


/*
 * Term in egraph
 */
void print_eterm(FILE *f, egraph_t *egraph, eterm_t t) {
  composite_t *c;

  c = egraph_term_body(egraph, t);
  if (atomic_body(c)) {
    print_eterm_id(f, t);
  } else {
    print_composite(f, c);
  }
}

void print_eterm_def(FILE *f, egraph_t *egraph, eterm_t t) {
  composite_t *c;
#if 0
  thvar_t x;
  etype_t tau;
#endif

  print_eterm_id(f, t);
  c = egraph_term_body(egraph, t);
  if (constant_body(c)) {
    fputs(" (constant)\n", f);
  } else if (c == VARIABLE_BODY) {
    fputs(" (variable)\n", f);
  } else if (c == NULL) {
    fputs(" (deleted)\n", f);
  } else {
    fputs(" := ", f);
    print_composite(f, c);
    fputc('\n', f);
  }

#if 0
  x = egraph_term_base_thvar(egraph, t);
  if (x != null_thvar) {
    fputs("   thvar: ", f);
    print_thvar(f, x);
    tau = egraph_term_type(egraph, t);
    fputs(", ", f);
    print_theory_id(f, tau);
    fputc('\n', f);
  }
#endif

}


void print_eterm_details(FILE *f, egraph_t *egraph, eterm_t t) {
  composite_t *c;

  fputs("--- Term ", f);
  print_eterm_id(f, t);
  fputs(" ---\n", f);

  c = egraph_term_body(egraph, t);
  if (constant_body(c)) {
    fputs("constant\n", f);
  } else if (c == VARIABLE_BODY) {
    fputs("variable\n", f);
  } else if (c == NULL) {
    fputs("deleted\n", f);
  } else {
    fputs("body: ", f);
    print_composite(f, c);
    fputc('\n', f);
  }

  if (c != NULL) {
    fputs("label: ", f);
    print_label(f, egraph_term_label(egraph, t));
    fputc('\n', f);
  }
}


static void print_list(FILE *f, egraph_t *egraph, occ_t t1) {
  occ_t t;

  t = t1;
  do {
    fputc(' ', f);
    print_occurrence(f, t);
    t = egraph_next(egraph, t);
  } while (t != t1);
}

void print_class(FILE *f, egraph_t *egraph, class_t c) {
  print_class_id(f, c);
  fputs(" := {", f);
  print_list(f, egraph, egraph_class_root(egraph, c));
  fputs(" }\n", f);
}


void print_class_details(FILE *f, egraph_t *egraph, class_t c) {
  occ_t root;
  eterm_t t;

  fputs("--- Class ", f);
  print_class_id(f, c);
  fputs("---\n", f);

  root = egraph_class_root(egraph, c);
  fputs("root: ", f);
  print_occurrence(f, root);
  fputc('\n', f);

  fputs("dmask: ", f);
  print_dmask(f, egraph_class_dmask(egraph, c));
  fputc('\n', f);

  fputs("type: ", f);
  print_etype(f, egraph_class_type(egraph, c));
  fputc('\n', f);

  fputs("thvar: ", f);
  print_thvar(f, egraph_class_thvar(egraph, c));
  fputc('\n', f);

  fputs("members: ", f);
  print_list(f, egraph, root);
  fputc('\n', f);

  fputs("member defs:\n", f);
  t = term_of_occ(root);
  do {
    fputs("  ", f);
    print_eterm_def(f, egraph, t);
    t = egraph_term_next(egraph, t);
  } while (t != term_of_occ(root));

  fputs("parents:\n", f);
  print_parents_details(f, egraph_class_parents(egraph, c));
  fputc('\n', f);
}


void print_class_of_occ(FILE *f, egraph_t *egraph, occ_t t) {
  fputs("class of ", f);
  print_occurrence(f, t);
  fputs(": ", f);
  print_label(f, egraph_label(egraph, t));
  fputs(" = {", f);
  print_list(f, egraph, t);
  fputs(" }\n", f);
}

void print_class_of_term(FILE *f, egraph_t *egraph, eterm_t t) {
  print_class_of_occ(f, egraph, pos_occ(t));
}



/*
 * Parents of all terms in t's class
 */
void print_parents_of_term(FILE *f, egraph_t *egraph, eterm_t t) {
  class_t c;

  fputs("parents of ", f);
  print_eterm_name(f, t);
  fputs(":\n", f);
  c = egraph_term_class(egraph, t);
  print_parents(f, egraph_class_parents(egraph, c));
}



/*
 * Egraph atom
 */
void print_egraph_atom(FILE *f, egraph_t *egraph, atom_t *atom) {
  fputc('[', f);
  print_bvar(f, atom->boolvar);
  fputs(" := ", f);
  print_eterm(f, egraph, atom->eterm);
  fputc(']', f);
}


void print_egraph_atom_of_literal(FILE *f, egraph_t *egraph, literal_t l) {
  void *atom;
  bvar_t v;

  v = var_of(l);
  assert(bvar_has_atom(egraph->core, v));
  atom = bvar_atom(egraph->core, v);
  assert(atom_tag(atom) == EGRAPH_ATM_TAG);
  if (is_neg(l)) {
    fputs("(not ", f);
  }
  print_eterm(f, egraph, ((atom_t *) untag_atom(atom))->eterm);
  if (is_neg(l)) {
    fputc(')', f);
  }
}



/*
 * Print definitions of all terms
 */
void print_egraph_terms(FILE *f, egraph_t *egraph) {
  composite_t *c;
  uint32_t i, n;
  thvar_t x;

  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    print_eterm_id(f, i);
    c = egraph_term_body(egraph, i);
    if (constant_body(c)) {
      fputs(" (constant)       ", f);
    } else if (c == VARIABLE_BODY) {
      fputs(" (variable)       ", f);
    } else if (c == NULL) {
      fputs(" (deleted)        ", f);
    } else {
      fputs(" := ", f);
      print_composite(f, c);
    }
    fputs("\t\t", f);
    print_type(f, egraph->types, egraph_term_real_type(egraph, i));
    //    fputs("\t\tetype = ", f);
    //    print_etype(f, egraph_class_type(egraph, i));
    x = egraph_term_base_thvar(egraph, i);
    if (x != null_thvar) {
      fputs("\t\t", f);
      switch(egraph_term_type(egraph, i)) {
      case ETYPE_INT:
        fprintf(f, "arith(i!%"PRId32")\t\t", x);
        break;
      case ETYPE_REAL:
        fprintf(f, "arith(z!%"PRId32")\t\t", x);
        break;
      case ETYPE_BV:
        fprintf(f, "bv(u!%"PRId32")\t\t", x);
        break;
      case ETYPE_FUNCTION:
        fprintf(f, "fun(f!%"PRId32")", x);
        break;
      case ETYPE_BOOL:
        fprintf(f, "lit(p!%"PRId32")\t\t", x);
        print_bval(f, bvar_value(egraph->core, x));
        break;
      case ETYPE_TUPLE:
        fprintf(f, "tup(g!%"PRId32")", x);
        break;
      default:
        fprintf(f, "BADTHVAR(%"PRId32")", x);
        break;
      }
    } else {
      if (egraph_term_is_true(egraph, i)) {
        fputs("\t\t(true term)", f);
      } else if (egraph_term_is_false(egraph, i)) {
        fputs("\t\t(false term)", f);
      }
    }

    fputc('\n', f);
  }
}

void print_egraph_terms_details(FILE *f, egraph_t *egraph) {
  uint32_t i, n;

  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    print_eterm_details(f, egraph, i);
  }
}

/*
 * Collect the root classes (and sort them)
 */
static void collect_root_classes(egraph_t *egraph, int_hset_t *roots) {
  uint32_t i, n;
  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    if (egraph->terms.body[i] != NULL) {
      int_hset_add(roots, egraph_term_class(egraph, i));
    }
  }
  int_hset_close(roots);

  // coercion to (int32_t *) is safe since class_ids are less than INT32_MAX
  int_array_sort((int32_t *)roots->data, roots->nelems);
}


void print_egraph_root_classes(FILE *f, egraph_t *egraph) {
  uint32_t i, n;
  int_hset_t roots;

  init_int_hset(&roots, 0);
  collect_root_classes(egraph, &roots);

  n = roots.nelems;
  for (i=0; i<n; i++) {
    print_class(f, egraph, roots.data[i]);
  }

  delete_int_hset(&roots);
}


void print_egraph_root_classes_details(FILE *f, egraph_t *egraph) {
  uint32_t i, n;
  int_hset_t roots;

  init_int_hset(&roots, 0);
  collect_root_classes(egraph, &roots);

  n = roots.nelems;
  for (i=0; i<n; i++) {
    print_class_details(f, egraph, roots.data[i]);
  }

  delete_int_hset(&roots);
}


/*
 * All atoms
 */
void print_egraph_atoms(FILE *f, egraph_t *egraph) {
  smt_core_t *core;
  uint32_t v, n;
  void *atm;

  core = egraph->core;
  if (core != NULL) {
    n = num_vars(core);
    for (v=0; v<n; v++) {
      atm = bvar_atom(core, v);
      if (atm != NULL && atom_tag(atm) == EGRAPH_ATM_TAG) {
        print_egraph_atom(f, egraph, untag_atom(atm));
        fputc('\n', f);
      }
    }
  }
}






/*
 * Sort all composites in array a in increasing order of id.
 * - n = size of the array
 */
static void qsort_composite_array(composite_t **a, uint32_t n);

static void isort_composite_array(composite_t **a, uint32_t n) {
  uint32_t i, j;
  composite_t *x, *y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (a[j]->id < x->id) j++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}

static void sort_composite_array(composite_t **a, uint32_t n) {
  if (n <= 10) {
    isort_composite_array(a, n);
  } else {
    qsort_composite_array(a, n);
  }
}

static void qsort_composite_array(composite_t **a, uint32_t n) {
  uint32_t i, j;
  composite_t *x, *y;
  uint32_t seed = PRNG_DEFAULT_SEED;

  // x = random pivot
  i = random_uint(&seed, n);
  x = a[i];

  // swap x and a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j--; } while (a[j]->id > x->id);
  do { i++; } while (i <= j && a[i]->id < x->id);

  while (i < j) {
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (a[j]->id > x->id);
    do { i++; } while (a[i]->id < x->id);
  }

  // pivot goes into a[j]
  a[0] = a[j];
  a[j] = x;

  // sort a[0...j-1] and a[j+1 .. n-1]
  sort_composite_array(a, j);
  j++;
  sort_composite_array(a + j, n - j);
}



/*
 * Collect all composites in the congruence table into vector v
 */
static void collect_congruence_roots(congruence_table_t *tbl, pvector_t *v) {
  uint32_t i, n;
  composite_t *tmp;

  n = tbl->size;
  for (i=0; i<n; i++) {
    tmp = tbl->data[i];
    if (tmp != NULL_COMPOSITE && tmp != DELETED_COMPOSITE) {
      pvector_push(v, tmp);
    }
  }
  sort_composite_array((composite_t **) v->data, v->size);
}



/*
 * Print a congruence root c = composite in the congruence table
 */
static void print_congruence_root(FILE *f, composite_t *c) {
  print_eterm_id(f, c->id);
  fputs(" := ", f);
  print_composite(f, c);
  fputc('\n', f);
}


void print_egraph_congruence_roots(FILE *f, egraph_t *egraph) {
  uint32_t i, n;
  pvector_t v;

  init_pvector(&v, 10);
  collect_congruence_roots(&egraph->ctable, &v);
  n = v.size;
  if (n > 0) {
    fputs("--- Congruence roots ---\n", f);
    for (i=0; i<n; i++) {
      print_congruence_root(f, v.data[i]);
    }
  } else {
    fputs("--- Empty congruence table ---\n", f);
  }

  delete_pvector(&v);
}


