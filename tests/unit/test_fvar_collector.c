/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
#include <gmp.h>

#include "include/yices.h"
#include "api/yices_globals.h"
#include "utils/int_vectors.h"
#include "terms/free_var_collector.h"
#include "io/term_printer.h"


/*
 * Global vector of terms + pretty printer
 */
static ivector_t all;
static yices_pp_t printer;


/*
 * Initialize the array of terms
 */
static term_t bin_app(term_t f, term_t x, term_t y) {
  term_t aux[2];

  aux[0] = x;
  aux[1] = y;
  return yices_application(f, 2, aux);
}

static term_t forall1(term_t var, term_t body) {
  return yices_forall(1, &var, body);
}

static term_t forall2(term_t var1, term_t var2, term_t body) {
  term_t aux[2];

  aux[0] = var1;
  aux[1] = var2;
  return yices_forall(2, aux, body);
}


static void init_terms(void) {
  type_t btype, rtype, utype, ftype1, ftype2;
  type_t aux[2];
  term_t x, y, z, a, b, f, g, p, q;

  btype = yices_bool_type();
  rtype = yices_real_type();
  utype = yices_new_uninterpreted_type();

  aux[0] = rtype;
  aux[1] = rtype;
  ftype1 = yices_function_type(2, aux, utype); // real, real -> utype

  aux[0] = utype;
  aux[1] = utype;
  ftype2 = yices_function_type(2, aux, btype); // utype, utype -> bool


  // x, y, z: real variables
  x = yices_new_variable(rtype);
  yices_set_term_name(x, "x");
  ivector_push(&all, x);

  y = yices_new_variable(rtype);
  yices_set_term_name(y, "y");
  ivector_push(&all, y);

  z = yices_new_variable(rtype);
  yices_set_term_name(z, "z");
  ivector_push(&all, z);

  // a, b: variables of type u
  a = yices_new_variable(utype);
  yices_set_term_name(a, "a");
  ivector_push(&all, a);

  b = yices_new_variable(utype);
  yices_set_term_name(b, "b");
  ivector_push(&all, b);

  // f, g: functions: [real, real -> utype]
  f = yices_new_uninterpreted_term(ftype1);
  yices_set_term_name(f, "f");
  ivector_push(&all, f);

  g = yices_new_uninterpreted_term(ftype1);
  yices_set_term_name(g, "g");
  ivector_push(&all, g);

  // p, q: predicates: [utype, utype -> bool]
  p = yices_new_uninterpreted_term(ftype2);
  yices_set_term_name(p, "p");
  ivector_push(&all, p);

  q = yices_new_uninterpreted_term(ftype2);
  yices_set_term_name(q, "q");
  ivector_push(&all, q);

  // composite terms
  ivector_push(&all, bin_app(f, x, x));
  ivector_push(&all, bin_app(f, x, y));
  ivector_push(&all, bin_app(f, x, z));
  ivector_push(&all, bin_app(f, y, x));
  ivector_push(&all, bin_app(f, y, y));
  ivector_push(&all, bin_app(f, y, z));
  ivector_push(&all, bin_app(f, z, x));
  ivector_push(&all, bin_app(f, z, y));
  ivector_push(&all, bin_app(f, z, z));

  ivector_push(&all, bin_app(g, x, x));
  ivector_push(&all, bin_app(g, x, y));
  ivector_push(&all, bin_app(g, x, z));
  ivector_push(&all, bin_app(g, y, x));
  ivector_push(&all, bin_app(g, y, y));
  ivector_push(&all, bin_app(g, y, z));
  ivector_push(&all, bin_app(g, z, x));
  ivector_push(&all, bin_app(g, z, y));
  ivector_push(&all, bin_app(g, z, z));

  ivector_push(&all, bin_app(p, a, b));
  ivector_push(&all, bin_app(p, bin_app(f, x, y), bin_app(g, y, x)));
  ivector_push(&all, bin_app(q, bin_app(g, x, x), a));
  ivector_push(&all, bin_app(q, bin_app(g, x, x), bin_app(f, x, z)));

  ivector_push(&all, yices_add(x, y));
  ivector_push(&all, yices_square(yices_sub(x, yices_int32(2))));
  ivector_push(&all, yices_arith_eq_atom(yices_add(x, z), yices_zero()));
  ivector_push(&all, yices_arith_eq_atom(yices_sub(x, z), yices_zero()));

  ivector_push(&all, yices_and2(bin_app(p, a, b), yices_arith_geq_atom(y, z)));
  ivector_push(&all, yices_or2(yices_arith_eq_atom(y, z), bin_app(q, b, a)));
  ivector_push(&all, yices_not(bin_app(q, a, a)));

  ivector_push(&all, forall1(a, yices_not(bin_app(q, a, a))));
  ivector_push(&all, forall1(b, yices_not(bin_app(q, a, a))));
  ivector_push(&all, forall2(x, y, yices_not(bin_app(q, a, a))));
  ivector_push(&all, forall2(x, y, yices_and2(yices_arith_eq_atom(x, y),
					      forall1(x, yices_arith_geq_atom(x, y)))));
  ivector_push(&all, yices_and2(forall2(x, y, bin_app(p, bin_app(f, x, y), bin_app(g, y, x))),
				forall2(y, x, bin_app(q, bin_app(g, x, x), bin_app(f, y, y)))));
}


/*
 * Show all the terms
 */
static void show_terms(void) {
  uint32_t i, n;
  term_t *v;

  n = all.size;
  v = all.data;
  for (i=0; i<n; i++) {
    printf("term[%02"PRIu32"]:  ", i);
    pp_term(&printer, __yices_globals.terms, v[i]);
    flush_yices_pp(&printer);
  }
}



/*
 * Display a set of variables
 */
static void show_set(harray_t *a) {
  uint32_t i, n;

  pp_open_block(&printer, PP_OPEN_PAR);
  n = a->nelems;
  for (i=0; i<n; i++) {
    pp_term(&printer, __yices_globals.terms, a->data[i]);
  }
  pp_close_block(&printer, true);
  flush_yices_pp(&printer);
}


/*
 * Test: compute the free variables of all terms
 */
static void test_collect(void) {
  fvar_collector_t collect;
  term_t *v;
  harray_t *a;
  uint32_t i, n;

  init_fvar_collector(&collect, __yices_globals.terms);

  n = all.size;
  v = all.data;
  for (i=0; i<n; i++) {
    a = get_free_vars_of_term(&collect, v[i]);
    printf("term[%02"PRIu32"]:  ", i);
    pp_term(&printer, __yices_globals.terms, v[i]);
    flush_yices_pp(&printer);
    printf("variables: ");
    show_set(a);
    printf("\n");
  }

  delete_fvar_collector(&collect);
}


int main(void) {
  pp_area_t area;

  yices_init();
  init_ivector(&all, 30);

  area.width = 80;
  area.height = UINT32_MAX;
  area.offset = 11;
  area.stretch = false;
  area.truncate = false;
  init_default_yices_pp(&printer, stdout, &area);

  init_terms();
  show_terms();
  test_collect();

  delete_yices_pp(&printer, false);
  delete_ivector(&all);
  yices_exit();

  return 0;
}
