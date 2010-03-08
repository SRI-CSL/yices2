#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

#include "types.h"
#include "terms.h"
#include "refcount_strings.h"

static arithvar_manager_t arith_manager;
static node_table_t bit_manager;
static bv_var_manager_t bv_manager;
static type_table_t type_tbl;
static term_table_t term_tbl;


/*
 * Print type i
 */
static void print_type_aux(FILE *f, type_table_t *table, type_t i, uint32_t level) {
  int32_t k;
  switch (type_kind(table, i)) {
  case UNUSED_TYPE:
    fprintf(f, "deleted");
    break;
  case BOOL_TYPE:
    fprintf(f, "bool");
    break;
  case INT_TYPE:
    fprintf(f, "int");
    break;
  case REAL_TYPE:
    fprintf(f, "real");
    break;
  case BITVECTOR_TYPE:
    fprintf(f, "(bitvector %"PRId32")", bv_type_size(table, i));
    break;
  case SCALAR_TYPE:
    fprintf(f, "(scalar %"PRId32" %s)", scalar_type_cardinal(table, i), type_name(table, i));
    break;
  case UNINTERPRETED_TYPE:
    fprintf(f, "(uninterpreted %s)", type_name(table, i));
    break;
  case TUPLE_TYPE:
    fprintf(f, "(tuple-type");
    for (k=0; k<tuple_type_ncomponents(table, i); k++) {
      fprintf(f, " %"PRId32, tuple_type_component(table, i, k));
    }
    fprintf(f, ")");
    break;
  case FUNCTION_TYPE:
    fprintf(f, "(fun-type:");
    for (k=0; k<function_type_ndomains(table, i); k++) {
      fprintf(f, " %"PRId32, function_type_domain(table, i, k));
    }
    fprintf(f, " -> %"PRId32")", function_type_range(table, i));
    break;
  default:
    fprintf(f, "(unknown kind %d)", type_kind(table, i));
    break;
  }

  if (level >= 1) {
    if (type_name(table, i) != NULL) {
      fprintf(f, ", name = %s", type_name(table, i));
    } else {
      fprintf(f, ", anonymous");
    }
  }
}


/*
 * Print term t
 */
static void print_term_aux(FILE *f, term_table_t *table, term_t t, uint32_t level) {
  int32_t k;
  term_t v;

  switch (term_kind(table, t)) {
  case UNUSED_TERM:
    fprintf(f, "deleted");
    return;
  case CONSTANT_TERM:
    fprintf(f, "(const %"PRId32" of type ", constant_term_index(table, t));
    print_type_aux(f, table->type_table, term_type(table, t), 0);
    fprintf(f, ")");
    break;
  case UNINTERPRETED_TERM:
    fprintf(f, "(uninterpreted of type ");
    print_type_aux(f, table->type_table, term_type(table, t), 0);
    fprintf(f, ")");    
    break;
  case VARIABLE:
    fprintf(f, "(var %"PRId32" of type ", variable_index(table, t));
    print_type_aux(f, table->type_table, term_type(table, t), 0);
    break;
  case NOT_TERM:
    fprintf(f, "(not %"PRId32")", not_term_arg(table, t));
    break;
  case ITE_TERM:
    fprintf(f, "(ite %"PRId32" %"PRId32" %"PRId32")", ite_term_cond(table, t), ite_term_then(table, t), ite_term_else(table, t));
    break;
  case EQ_TERM:
    fprintf(f, "(eq %"PRId32" %"PRId32")", eq_term_left(table, t), eq_term_right(table, t));
    break;
  case APP_TERM:
    fprintf(f, "(app %"PRId32" to", app_term_fun(table, t));
    for (k=0; k<app_term_nargs(table, t); k++) {
      fprintf(f, " %"PRId32, app_term_arg(table, t, k));
    }
    fprintf(f, ")");
    break;
  case OR_TERM:
    fprintf(f, "(or");
    for (k=0; k<or_term_nargs(table, t); k++) {
      fprintf(f, " %"PRId32, or_term_arg(table, t, k));
    }
    fprintf(f, ")");
    break;
  case TUPLE_TERM:
    fprintf(f, "(mk-tuple");
    for (k=0; k<tuple_term_nargs(table, t); k++) {
      fprintf(f, " %"PRId32, tuple_term_arg(table, t, k));
    }
    fprintf(f, ")");
    break;
  case SELECT_TERM:
    fprintf(f, "(select %"PRId32" %"PRId32")", select_term_arg(table, t), select_term_index(table, t));
    break;
  case UPDATE_TERM:
    fprintf(f, "(update %"PRId32" at", update_term_fun(table, t));
    for (k=0; k<update_term_nargs(table, t); k++) {
      fprintf(f, " %"PRId32, update_term_arg(table, t, k));
    }
    fprintf(f, " with %"PRId32")", update_term_newval(table, t));
    break;

  case FORALL_TERM:
    fprintf(f, "(forall (");
    for (k=0; k<forall_term_nvars(table, t); k++) {
      v = forall_term_var(table, t, k);
      if (k == 0) {
	fprintf(f, "x_%"PRId32"::", variable_index(table, v));
      } else {
	fprintf(f, " x_%"PRId32"::", variable_index(table, v));
      }
      print_type_aux(f, table->type_table, term_type(table, v), 0);
    }
    fprintf(f, ") %"PRId32")", forall_term_body(table, t));
    break;

  case ARITH_TERM:
    fprintf(f, "arith-term");
    break;
  case ARITH_EQ_ATOM:
    fprintf(f, "arith-eq-atom");
    break;
  case ARITH_GE_ATOM:
    fprintf(f, "arith-ge-atom");
    break;
  case BV_LOGIC_TERM:
    fprintf(f, "bv-logic-term");
    break;
  case BV_ARITH_TERM:
    fprintf(f, "bv-arith-term");
    break;
  case BV_CONST_TERM:
    fprintf(f, "bv-const-term");
    break;
  case BV_EQ_ATOM:
    fprintf(f, "bv-eq-atom");
    break;
  case BV_GE_ATOM:
    fprintf(f, "bv-ge-atom");
    break;
  case BV_SGE_ATOM:
    fprintf(f, "bv-sge-atom");
    break;

  default:
    fprintf(f, "(unknown kind %u)", term_kind(table, t));
    break;
  }

  if (level >= 1) {
    if (term_name(table, t) != NULL) {
      fprintf(f, ", name = %s, type = ", term_name(table, t));
    } else {
      fprintf(f, ", anonymous, type = ");
    }    
    print_type_aux(f, table->type_table, term_type(table, t), 0);    
  }
}

static void print_term_table(FILE *f, term_table_t *table, uint32_t level) {
  uint32_t t;
  int32_t k, l;

  fprintf(f, "term table %p\n", table);
  fprintf(f, "  size = %"PRIu32"\n", table->size);
  fprintf(f, "  nelems = %"PRIu32"\n", table->nelems);
  for (t=0; t<table->nelems; t++) {
    fprintf(f, "  term %"PRId32": ", t);
    print_term_aux(f, table, t, level);
    fprintf(f, "\n");
  }

  if (level >= 2) {
    fprintf(f, "  root terms:");
    l = 8;
    for (t=0; t<table->nelems; t++) {
      if (tst_bit(table->root, t)) {
	l --;
	if (l == 0) {
	  l = 8;
	  fprintf(f, "\n      ");
	}
	fprintf(f, " %"PRId32, t);
      }
    }
    fprintf(f, "\n");
  }

  if (level >= 2) {
    k = table->free_idx;
    if (k < 0) {
      fprintf(f, "  free list: empty\n");
    } else {
      fprintf(f, "  free list:");
      l = 8;
      do {
	l --;
	if (l == 0) {
	  l = 8;
	  fprintf(f, "\n      ");
	}
	fprintf(f, " %"PRId32, k);
	k = table->desc[k].integer;
      } while (k >= 0);
      fprintf(f, "\n");
    }
  }
}



int main() {
  term_table_t *terms;
  type_table_t *types;
  type_t any;
  term_t a, b, c, d, e, f, g, h;

  terms = &term_tbl;
  types = &type_tbl;

  init_type_table(types, 0);
  init_node_table(&bit_manager, 0);
  init_bv_var_manager(&bv_manager, 10, &bit_manager);
  init_arithvar_manager(&arith_manager, 10);
  init_term_table(terms, 0, types, &arith_manager, &bv_manager);
 
  print_term_table(stdout, terms, 10);
  printf("---\n\n");

  a = true_term(terms);
  b = false_term(terms);
  c = constant_term(terms, bool_type(types), 0);
  d = constant_term(terms, bool_type(types), 1);

  printf("a = %"PRId32" (true_term)\n", a);
  printf("b = %"PRId32" (false_term)\n", b);
  printf("c = %"PRId32" (constant_term bool 0)\n", c);
  printf("d = %"PRId32" (constant_term bool 1)\n", d);
  printf("\n");
  print_term_table(stdout, terms, 1);
  printf("---\n\n");


  any = new_uninterpreted_type(types);
  set_type_name(types, any, clone_string("any"));
  a = constant_term(terms, any, 2);
  b = constant_term(terms, any, 4);
  c = constant_term(terms, any, 2);
  d = constant_term(terms, any, 4);
  printf("a = %"PRId32" (constant_term any 2)\n", a);
  printf("b = %"PRId32" (constant_term any 4)\n", b);
  printf("c = %"PRId32" (constant_term any 2)\n", c);
  printf("d = %"PRId32" (constant_term any 4)\n", d);
  printf("\n");
  print_term_table(stdout, terms, 1);
  printf("---\n\n");


  e = new_uninterpreted_term(terms, bool_type(types));
  set_term_name(terms, e, clone_string("var_e"));
  g = new_uninterpreted_term(terms, any);
  set_term_name(terms, g, clone_string("var_e"));
  h = new_uninterpreted_term(terms, any);
  set_term_name(terms, h, clone_string("true"));
  printf("e = %"PRId32" (bool var_e)\n", e);
  printf("g = %"PRId32" (any var_e)\n", g);
  printf("h = %"PRId32" (any true)\n", h);
  printf("\n");
  print_term_table(stdout, terms, 1);
  printf("---\n\n");


  f = ite_term(terms, e, a, b, any);
  g = ite_term(terms, e, a, b, any);
  h = ite_term(terms, e, b, a, any);
  printf("f = %"PRId32" (ite e a b)\n", f);
  printf("g = %"PRId32" (ite e a b)\n", g);
  printf("h = %"PRId32" (ite e b a)\n", h);
  printf("\n");
  print_term_table(stdout, terms, 1);
  printf("---\n\n");

  set_root_term_flag(terms, g);
  printf("\n\n*** GARBAGE COLLECTION ***\n\n");
  term_table_garbage_collection(terms);
  print_term_table(stdout, terms, 1);
  printf("---\n\n\n");


  
  delete_term_table(terms);
  delete_type_table(types);
  delete_arithvar_manager(&arith_manager);
  delete_bv_var_manager(&bv_manager);
  delete_node_table(&bit_manager);

  return 0;
}
