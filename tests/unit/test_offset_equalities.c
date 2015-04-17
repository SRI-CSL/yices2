/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <inttypes.h>
#include <stdio.h>

#include "solvers/simplex/offset_equalities.h"
#include "utils/assert_utils.h"
#include "utils/int_vectors.h"


/*
 * Construct variables and polynomials for testing
 * - for each i in 0 .. NVARS-1
 * - var[i] = arithmetic variable for i
 *   term[i] = egraph term for i
 * - poly[i] = NULL if var[i] is a free variable
 * - poly[i] = a polynomial otherwise
 *
 *
 * We use
 * - poly[0] = 0                   var[0] = 10     term[0] = 20
 * - poly[1] = 1                   var[1] = 11     term[1] = 21
 * - poly[2] = -100                var[2] = 12     term[2] = 22
 * - poly[3] = NULL (x3)           var[3] = 3      term[3] = 23
 * - poly[4] = NULL (x4)           var[4] = 4      term[4] = 24
 * - poly[5] = NULL (x5)           var[5] = 5      term[5] = 25
 * - poly[6] = x3 - x4             var[6] = 6      term[6] = 26
 * - poly[7] = x5 - x4             var[7] = 7      term[7] = 27
 * - poly[8] = 2 + x3 + x4         var[8] = 8      term[8] = 28
 * - poly[9] = x3 + 2 * x5         var[9] = 9      term[9] = 29
 */
#define NPOLYS 10

static polynomial_t *poly[NPOLYS];

static int32_t var[NPOLYS] = {
  10, 11, 12, 3, 4, 5, 6, 7, 8, 9,
};

static int32_t term[NPOLYS] = {
  20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
};



/*
 * Build a polynomial:
 * - a = coefficient array
 * - x = variable array
 * - n = number of coefficients
 *
 * a[0] is the constant (x[0] is ignored)
 */
static polynomial_t *make_poly(poly_buffer_t *b, int32_t *a, int32_t *x, uint32_t n) {
  rational_t q;
  uint32_t i;

  assert(n > 0);

  q_init(&q);
  reset_poly_buffer(b);

  q_set32(&q, a[0]);
  poly_buffer_add_const(b, &q);

  for (i=1; i<n; i++) {
    q_set32(&q, a[i]);
    poly_buffer_add_monomial(b, x[i], &q);
  }

  normalize_poly_buffer(b);
  q_clear(&q);

  return poly_buffer_get_poly(b);
}

static void build_polys(void) {
  poly_buffer_t aux;
  int32_t a[4];
  int32_t x[4];

  init_poly_buffer(&aux);
  a[0] = 0;
  poly[0] = make_poly(&aux, a, NULL, 1);  // 0

  a[0] = 1;
  poly[1] = make_poly(&aux, a, NULL, 1); // 1

  a[0] = -100;
  poly[2] = make_poly(&aux, a, NULL, 1); // -100

  poly[3] = NULL;
  poly[4] = NULL;
  poly[5] = NULL;

  a[0] = 0;
  a[1] = 1;  x[1] = 3;
  a[2] = -1; x[2] = 4;
  poly[6] = make_poly(&aux, a, x, 3); // x3 - x4

  a[0] = 0;
  a[1] = 1;  x[1] = 5;
  a[2] = -1; x[2] = 4;
  poly[7] = make_poly(&aux, a, x, 3); // x5 - x4

  a[0] = 2;
  a[1] = 1; x[1] = 3;
  a[2] = 1; x[2] = 4;
  poly[8] = make_poly(&aux, a, x, 3); // 2 + x3 + x4

  a[0] = 0;
  a[1] = 1; x[1] = 3;
  a[2] = 2; x[2] = 5;
  poly[9] = make_poly(&aux, a, x, 3); // x3 + 2 * x5

  delete_poly_buffer(&aux);
}


static void delete_polys(void) {
  uint32_t i;

  for (i=0; i<NPOLYS; i++) {
    if (poly[i] != NULL) {
      free_polynomial(poly[i]);
    }
  }
}


// variable that corresponds to term t
static int32_t var_of_term(int32_t t) {
  uint32_t i;

  for (i=0; i<NPOLYS; i++) {
    if (term[i] == t) {
      return var[i];
    }
  }

  assert(false);

  return -1;
}

/*
 * Print stuff
 */
static void print_mono(const char *prefix, rational_t *coeff, int32_t x, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      printf("-");
      if (x != const_idx) {
	printf(" ");
      }
    } else {
      printf(" - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      printf(" + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (x == const_idx) {
    q_print_abs(stdout, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(stdout, coeff);
      printf(" * ");
    }
    printf("%s%"PRId32, prefix, x);
  }
}

static void show_poly(polynomial_t *p) {
  uint32_t i, n;
  bool first;

  if (polynomial_is_zero(p)) {
    printf("0");
  } else {
    n = p->nterms;
    first = true;
    for (i=0; i<n; i++) {
      print_mono("x", &p->mono[i].coeff, p->mono[i].var, first);
      first = false;
    }
  }
}

static void show_polys(void) {
  uint32_t i;

  printf("===== Polynomials =====\n");
  for (i=0; i<NPOLYS; i++) {
    if (poly[i] != NULL) {
      printf("x%"PRId32" := ", var[i]);
      show_poly(poly[i]);
      printf("\n");
    }
  }
  printf("\n");
}



/*
 * Offset manager
 */
static void show_poly_buffer(poly_buffer_t *b) {
  monomial_t *mono;
  uint32_t i, n;
  bool first;

  n = poly_buffer_nterms(b);
  mono = poly_buffer_mono(b);
  if (n == 0) {
    printf("0");
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_mono("z", &mono[i].coeff, mono[i].var, first);
      first = false;
    }
  }
}

static void print_normal_form(offset_table_t *table, polynomial_t *p) {
  poly_buffer_t aux;
  offset_desc_t *d;
  uint32_t i, n;
  thvar_t x;
  int32_t j;

  init_poly_buffer(&aux);
  n = p->nterms;
  for (i=0; i<n; i++) {
    if (p->mono[i].var == const_idx) {
      assert(i == 0);
      poly_buffer_add_const(&aux, &p->mono[i].coeff);
    } else {
      x = p->mono[i].var;
      assert(0 <= x && x < table->var2offset_var.size);
      j = table->var2offset_var.data[x];
      assert(0 < j && j < table->nvars);

      d = table->desc + j;
      poly_buffer_addmul_monomial(&aux, const_idx, &p->mono[i].coeff, &d->offset);
      if (d->root > 0) {
	poly_buffer_add_monomial(&aux, d->root, &p->mono[i].coeff);
      }
    }
  }

  normalize_poly_buffer(&aux);
  show_poly_buffer(&aux);
  delete_poly_buffer(&aux);
}

static void print_var_array(var_array_t *a) {
  uint32_t i, n;

  if (a == NULL) {
    printf("nil");
  } else {
    n = a->ndeps;
    if (n == 0) {
      printf("[]");
    } else {
      n = a->ndeps;
      printf("[");
      for (i=0; i<n; i++) {
	printf(" (z%"PRId32", %"PRIu32")", a->data[i].var, a->data[i].idx);
      }
      printf(" ]");
    }
  }
}

static void print_flag(bool x) {
  if (x) {
    printf("1");
  } else {
    printf("0");
  }
}

static void print_ptable(offset_manager_t *mngr) {
  offset_poly_table_t *table;
  uint32_t i, n;

  table = &mngr->ptable;
  printf("===== ptable ====\n");
  n = table->npolys;
  for (i=0; i<n; i++) {
    printf("poly[%"PRIu32"] := ", i);
    show_poly(table->def[i]);
    printf("        (eterm: t!%"PRId32, table->eterm[i]);
    printf(", active: ");
    print_flag(tst_bit(table->active, i));
    printf(", mark: ");
    print_flag(tst_bit(table->mark, i));
    printf(")\n");
    printf("   normal form: ");
    print_normal_form(&mngr->vtable, table->def[i]);
    printf("\n");
    printf("   vars: ");
    print_var_array(table->vars[i]);
    printf("\n");
  }
  printf("\n");
}

static void print_var2poly(offset_manager_t *mngr) {
  remap_array_t *map;
  uint32_t i, n;

  map = &mngr->ptable.var2poly;
  n = map->size;
  printf("==== var2poly map ====\n");
  for (i=0; i<n; i++) {
    if (map->data[i] >= 0) {
      printf(" var2poly[%"PRIu32"] = %"PRId32"\n", i, map->data[i]);
    }
  }
  printf("\n");
}

static void print_dep(dep_t *v) {
  uint32_t i, n;
  bool first;
  int32_t k;

  if (v == NULL) {
    printf("nil");
  } else {
    first = true;
    printf("{");
    n = v->nelems;
    for (i=0; i<n; i++) {
      k = v->data[i];
      if (k >= 0) {
	if (first) {
	  printf("%"PRId32, k);
	  first = false;
	} else {
	  printf(", %"PRId32, k);
	}
      }
    }
    printf("}");
  }
}

static void print_vtable(offset_manager_t *mngr) {
  offset_table_t *table;
  offset_desc_t *d;
  uint32_t i, n;

  table = &mngr->vtable;

  printf("===== vtable ====\n");
  n = table->nvars;
  for (i=0; i<n; i++) {
    d = table->desc + i;
    printf("z%"PRIu32" = z%"PRId32, i, d->root);
    if (q_is_neg(&d->offset)) {
      printf(" - ");
    } else {
      printf(" + ");
    }
    q_print_abs(stdout, &d->offset);
    printf("\n");
    printf("   dep: ");
    print_dep(table->dep[i]);
    printf("\n");
  }
}

static void print_var2offset_var(offset_manager_t *mngr) {
  remap_array_t *map;
  uint32_t i, n;

  map = &mngr->vtable.var2offset_var;
  n = map->size;
  printf("==== renaming: var2offset var ====\n");
  for (i=0; i<n; i++) {
    if (map->data[i] >= 0) {
      printf("var2offset_var[x%"PRIu32"] = z%"PRId32"\n", i, map->data[i]);
    }
  }
  printf("\n");
}



/*
 * Global manager
 */
static offset_manager_t mngr;


/*
 * Get explanation for t1 == t2
 */
static void test_eq_explanation(eterm_t t1, eterm_t t2) {
  ivector_t v;
  uint32_t i, n;
  int32_t x1, x2;

  init_ivector(&v, 10);

  x1 = var_of_term(t1);
  x2 = var_of_term(t2);
  offset_manager_explain_equality(&mngr, x1, x2, &v);

  printf("---> Explanation:");
  n = v.size;
  for (i=0; i<n; i++) {
    printf(" eq[%"PRId32"]", v.data[i]);
  }
  printf("\n\n");

  delete_ivector(&v);
}

/*
 * Callback to report equality
 */
static void notify_equality(void *aux, eterm_t t1, eterm_t t2) {
  printf("---> t!%"PRId32" == t!%"PRId32"\n", t1, t2);
  fflush(stdout);
  test_eq_explanation(t1, t2);
}

static void test_equality(int32_t x, int32_t y, int32_t offset, int32_t id) {
  rational_t q;

  printf("\n\n*** Asserting: eq[%"PRId32"]: ", id);
  if (x < 0) {
    printf("0 = ");
  } else {
    printf("x%"PRId32" = ", x);
  }
  if (y < 0) {
    printf("%"PRId32" ****\n", offset);
  } else {
    printf("x%"PRId32, y);
    if (offset > 0) {
      printf(" + %"PRId32" ****\n", offset);
    } else if (offset< 0) {
      printf(" - %"PRId32" ****\n", -offset);
    } else {
      printf(" ****\n");
    }
  }

  q_init(&q);
  q_set32(&q, offset);
  assert_offset_equality(&mngr, x, y, &q, id);
  q_clear(&q);
}


// Used assert_true instead of assert to prevent compiler warnings
int main(void) {
  uint32_t i;
  bool ok;

  init_rationals();
  build_polys();
  show_polys();

  init_offset_manager(&mngr, NULL, notify_equality);

  /*
   * FIRST TESTS
   */
  for (i=0; i<NPOLYS; i++) {
    record_offset_poly(&mngr, term[i], var[i], poly[i]);
  }

  printf("\n*** Initial state ****\n");
  print_var2poly(&mngr);
  print_var2offset_var(&mngr);
  print_ptable(&mngr);
  print_vtable(&mngr);


  ok = offset_manager_propagate(&mngr);
  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  offset_manager_increase_decision_level(&mngr);
  test_equality(var[3], var[4], 0, 123);
  ok = offset_manager_propagate(&mngr);

  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  offset_manager_backtrack(&mngr, 0);
  printf("\n*** After backtracking to level 0 ***\n");
  print_ptable(&mngr);
  print_vtable(&mngr);

  offset_manager_increase_decision_level(&mngr);
  test_equality(var[3], -1, 1, 234);
  test_equality(var[3], var[4], 0, 123);
  ok = offset_manager_propagate(&mngr);
  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  offset_manager_backtrack(&mngr, 0);
  ok = offset_manager_propagate(&mngr);
  printf("\n*** After backtracking to level 0 ***\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  /*
   * SECOND TEST
   */
  reset_offset_manager(&mngr);
  printf("\n*** After reset ****\n");
  print_var2poly(&mngr);
  print_var2offset_var(&mngr);
  print_ptable(&mngr);
  print_vtable(&mngr);


  for (i=0; i<NPOLYS/2; i++) {
    record_offset_poly(&mngr, term[i], var[i], poly[i]);
  }
  offset_manager_push(&mngr);

  printf("\n*** After push ****\n");
  print_var2poly(&mngr);
  print_var2offset_var(&mngr);
  print_ptable(&mngr);
  print_vtable(&mngr);

  while (i < NPOLYS) {
    record_offset_poly(&mngr, term[i], var[i], poly[i]);
    i ++;
  }

  printf("\n*** After adding all polys ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);


  test_equality(var[5], var[3], 10, 111);
  ok = offset_manager_propagate(&mngr);
  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  offset_manager_pop(&mngr);
  printf("\n*** After pop ****\n");
  print_var2poly(&mngr);
  print_var2offset_var(&mngr);
  print_ptable(&mngr);
  print_vtable(&mngr);

  test_equality(var[4], var[3], 10, 111);
  ok = offset_manager_propagate(&mngr);
  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  /*
   * THIRD TEST
   */
  reset_offset_manager(&mngr);
  printf("\n*** After reset ****\n");
  print_var2poly(&mngr);
  print_var2offset_var(&mngr);
  print_ptable(&mngr);
  print_vtable(&mngr);

  for (i=0; i<6; i++) {
    record_offset_poly(&mngr, term[i], var[i], poly[i]);
  }
  test_equality(var[5], var[3], 10, 111);
  ok = offset_manager_propagate(&mngr);
  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  offset_manager_push(&mngr);

  printf("\n*** After push ****\n");
  print_var2poly(&mngr);
  print_var2offset_var(&mngr);
  print_ptable(&mngr);
  print_vtable(&mngr);

  while (i < NPOLYS) {
    record_offset_poly(&mngr, term[i], var[i], poly[i]);
    i ++;
  }

  printf("\n*** After adding all polys ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);

  test_equality(var[4], var[3], 10, 111);
  test_equality(-1, var[3], 56, 122);
  ok = offset_manager_propagate(&mngr);
  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  offset_manager_pop(&mngr);

  printf("\n*** After pop ****\n");
  print_var2poly(&mngr);
  print_var2offset_var(&mngr);
  print_ptable(&mngr);
  print_vtable(&mngr);

  ok = offset_manager_propagate(&mngr);
  printf("\n*** After propagate ****\n");
  print_ptable(&mngr);
  print_vtable(&mngr);
  assert_true(ok);

  delete_offset_manager(&mngr);
  delete_polys();
  cleanup_rationals();

  return 0;
}
