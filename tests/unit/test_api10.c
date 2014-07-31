/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST TERM SUBSTITUTIONS
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

#include "yices.h"

/*
 * Arrays of terms for testing: we store term + its type
 * - unint[i] = uninterpreted term
 * - var[i] = variable
 * - range = array of terms: all substitutions are maps from
 *   elements of unint and var to elements of range
 * - test = array of terms (to which we apply substitutions)
 */
typedef struct typed_term_s {
  term_t term;
  type_t type;
} typed_term_t;

#define BASE_TYPES 5
#define NUNINTS  10
#define NVARS    10
#define NRANGES  50
#define NTESTS   64

static type_t base_type[BASE_TYPES];

static typed_term_t unint[NUNINTS];
static typed_term_t var[NVARS];
static typed_term_t range[NRANGES];

static term_t test[NTESTS];


/*
 * Function type: [tau1, tau2 -> sigma]
 */
static type_t binary_ftype(type_t tau1, type_t tau2, type_t sigma) {
  type_t aux[2] = { tau1, tau2 };
  return yices_function_type(2, aux, sigma);
}


/*
 * Create a variable or uninterpreted term of type tau, with the given name
 * - store the result into d
 */
static void new_var(typed_term_t *d, type_t tau, const char *name) {
  term_t v;

  v = yices_new_variable(tau);
  yices_set_term_name(v, name);
  d->term = v;
  d->type = tau;
}

static void new_unint(typed_term_t *d, type_t tau, const char *name) {
  term_t t;

  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, name);
  d->term = t;
  d->type = tau;
}



/*
 * Initialize the base types, unint, and var arrays
 */
static void init_domain(void) {
  type_t t_int, t_real, t_bool, t_bv, t_u;

  t_int = yices_int_type();
  t_real = yices_real_type();
  t_bool = yices_bool_type();
  t_bv = yices_bv_type(32);
  t_u = yices_new_uninterpreted_type();
  yices_set_type_name(t_u, "U");

  base_type[0] = t_int;
  base_type[1] = t_real;
  base_type[2] = t_bool;
  base_type[3] = t_bv;
  base_type[4] = t_u;

  new_var(&var[0], t_int, "i0");
  new_var(&var[1], t_int, "i1");
  new_var(&var[2], t_real, "x0");
  new_var(&var[3], t_real, "x1");
  new_var(&var[4], t_bool, "p0");
  new_var(&var[5], t_bool, "p1");
  new_var(&var[6], t_bv, "u0");
  new_var(&var[7], t_bv, "u1");
  new_var(&var[8], t_u, "v0");
  new_var(&var[9], t_u, "v1");

  new_unint(&unint[0], t_int, "I0");
  new_unint(&unint[1], t_int, "I1");
  new_unint(&unint[2], t_real, "X0");
  new_unint(&unint[3], t_real, "X1");
  new_unint(&unint[4], t_bool, "P0");
  new_unint(&unint[5], t_bool, "P1");
  new_unint(&unint[6], t_bv, "U0");
  new_unint(&unint[7], t_bv, "U1");
  new_unint(&unint[8], t_u, "V0");
  new_unint(&unint[9], t_u, "V1");
}


/*
 * Initialize the range terms
 * - first copy all vars and unint then generate constants
 */
static void init_range(void) {
  uint32_t i;
  term_t t;
  type_t tau;

  for (i=0; i<NVARS; i++) {
    range[i] = var[i];
  }
  for (i=0; i<NUNINTS; i++) {
    range[i + NVARS] = unint[i];
  }

  range[20].term = yices_int32(0);
  range[20].type = yices_int_type();
  range[21].term = yices_int32(1);
  range[21].type = yices_int_type();
  range[22].term = yices_int32(-2);
  range[22].type = yices_int_type();
  range[23].term = yices_rational32(1, 2);
  range[23].type = yices_real_type();
  range[24].term = yices_rational32(-3, 2);
  range[24].type = yices_real_type();
  range[25].term = yices_true();
  range[25].type = yices_bool_type();
  range[26].term = yices_false();
  range[26].type = yices_bool_type();
  range[27].term = yices_bvconst_uint32(32, 0);
  range[27].type = yices_bv_type(32);
  range[28].term = yices_bvconst_uint32(32, 0x55555555u);
  range[28].type = yices_bv_type(32);
  range[29].term = yices_bvconst_uint32(32, 0x80000000u);
  range[29].type = yices_bv_type(32);

  range[30].term = yices_constant(base_type[4], 0);
  range[30].type = base_type[4];
  yices_set_term_name(range[30].term, "a");
  range[31].term = yices_constant(base_type[4], 1);
  range[31].type = base_type[4];
  yices_set_term_name(range[31].term, "b");

  // more arithmetic terms
  new_unint(&range[32], yices_int_type(), "X");
  new_unint(&range[33], yices_int_type(), "Y");
  new_unint(&range[34], yices_int_type(), "Z");

  t = yices_parse_term("(+ x0 x1 i0 i1)");
  tau = yices_type_of_term(t);
  range[35].term = t;
  range[35].type = tau;

  t = yices_parse_term("(+ x0 x1 i0 i1 X Y Z)");
  tau = yices_type_of_term(t);
  range[36].term = t;
  range[36].type = tau;

  t = yices_parse_term("(and (<= 0 x0) (<= x0 10))");
  tau = yices_type_of_term(t);
  range[37].term = t;
  range[37].type = tau;

  // f: [real, real -> real]
  tau = binary_ftype(yices_real_type(), yices_real_type(), yices_real_type());
  new_unint(&range[38], tau, "f");

  t = yices_parse_term("(f 0 X)");
  tau = yices_type_of_term(t);
  range[39].term = t;
  range[39].type = tau;

  t = yices_parse_term("(f 0 i0)");
  tau = yices_type_of_term(t);
  range[40].term = t;
  range[40].type = tau;

  t = yices_parse_term("(+ 2 (f X X) (f Y Y))");
  tau = yices_type_of_term(t);
  range[41].term = t;
  range[41].type = tau;

  // more bitvector terms
  new_unint(&range[42], base_type[3], "D0");
  new_unint(&range[43], base_type[3], "D1");

  t = yices_parse_term("(bv-and D0 D1)");
  tau = yices_type_of_term(t);
  range[44].term = t;
  range[44].type = tau;

  t = yices_parse_term("(bv-add D0 D1)");
  tau = yices_type_of_term(t);
  range[44].term = t;
  range[44].type = tau;

  t = yices_parse_term("(bv-add u0 D1)");
  tau = yices_type_of_term(t);
  range[44].term = t;
  range[44].type = tau;

  t = yices_parse_term("(bv-mul D0 D1)");
  tau = yices_type_of_term(t);
  range[45].term = t;
  range[45].type = tau;

  t = yices_parse_term("(bv-mul D0 D1)");
  tau = yices_type_of_term(t);
  range[46].term = t;
  range[46].type = tau;

  t = yices_parse_term("(bv-xor D0 D1)");
  tau = yices_type_of_term(t);
  range[47].term = t;
  range[47].type = tau;

  t = yices_parse_term("(bv-xor u0 u1)");
  tau = yices_type_of_term(t);
  range[48].term = t;
  range[48].type = tau;

  // more uninterpreted term
  new_unint(&range[49], base_type[3], "TEST");
}


/*
 * Initialize the test array: everything in range is stored first
 * then we build more terms.
 */
static void init_test(void) {
  uint32_t i;

  for (i=0; i<NRANGES; i++) {
    test[i] = range[i].term;
  }
  assert(i == 50);

  test[50] = yices_parse_term("(f X X)");
  test[51] = yices_parse_term("(f X Y)");
  test[52] = yices_parse_term("(f (+ x0 x1) (+ i0 i1))");
  test[53] = yices_parse_term("(+ x0 x1 1)");
  test[54] = yices_parse_term("(or (= (f x0 x0) (f x1 x1)) (<= x0 i0) (<= i0 (f x0 i1)))");
  test[55] = yices_parse_term("(^ (+ x0 x1) 2)");
  test[56] = yices_parse_term("(exists (x::int) (> (f x x) 0))");
  test[57] = yices_parse_term("(exists (x0::real y0::real) (= (f (+ x0 y0 x1) 10) i1))");
  test[58] = yices_parse_term("(or (forall (x0::real) (> (f x0 x0) 0)) (exists (x0::real) (<= (f x0 x0) 20)))");
  test[59] = yices_parse_term("(and p0 p1 (= (ite (/= v0 a) a b) v1))");
  test[60] = yices_parse_term("(and (not p0) p1 (or (not P0) (not P1)))");
  test[61] = yices_parse_term("(distinct x0 x1 i0 i1)");
  test[62] = yices_parse_term("(distinct x0 x1 i0 i1 I0)");
  test[63] = yices_parse_term("(distinct x0 x1 1 2 I0 I1)");


}



/*
 * Pretty print the whole list
 */
static void show_range(void) {
  uint32_t i;

  for (i=0; i<50; i++) {
    printf("range[%02"PRIu32"]: ", i);
    yices_pp_term(stdout, range[i].term, 100, 20, 11);
    printf("     type: ");
    yices_pp_type(stdout, range[i].type, 100, 20, 11);
  }
  printf("\n");
}

static void show_test(void) {
  uint32_t i;

  for (i=0; i<NTESTS; i++) {
    printf("test[%02"PRIu32"]: ", i);
    yices_pp_term(stdout, test[i], 100, 20, 10);
  }
  printf("\n");
}


/*
 * Print a substitution:
 * - v = array of variables or uninterpreted terms
 * - s = what they must be replaced by
 * - n = number of elements in v and s
 */
static void show_substitution(uint32_t n, term_t *v, term_t *s) {
  const char *name;
  uint32_t i, len;

  printf("Substitution:\n");
  for (i=0; i<n; i++) {
    name = yices_get_term_name(v[i]);
    len = strlen(name) + 6;
    printf("%s ---> ", name);
    yices_pp_term(stdout, s[i], 100, 20, len);
  }
}

/*
 * Test: apply substitution defined by v and s to term t
 * - v and m must have n elements
 * - all elements of v must be terms in var or unint
 */
static void test_substitution(uint32_t n, term_t *v, term_t *s, term_t t) {
  term_t u;

  show_substitution(n, v, s);
  printf("Input term: ");
  yices_pp_term(stdout, t, 100, 20, 12);
  u = yices_subst_term(n, v, s, t);
  if (u < 0) {
    printf("Error: ");
    yices_print_error(stdout);
  } else {
    printf("Result: ");
    yices_pp_term(stdout, u, 100, 20, 8);
  }
  printf("\n");
}


/*
 * Search for a term in map whose type is a subtype of tau
 * - i = where to start the search
 * - return -1 if there's no match
 */
static term_t find_map(type_t tau, uint32_t i) {
  uint32_t j;

  assert(i < NRANGES);
  j = i;
  do {
    if (yices_test_subtype(range[j].type, tau)) {
      return range[j].term;
    }
    j ++;
    if (j >= NRANGES) j = 0;
  } while (i != j);

  return NULL_TERM;
}




int main(void) {
  term_t v[4], s[4];
  uint32_t i;

  yices_init();
  init_domain();
  init_range();
  init_test();
  show_range();
  show_test();

  v[0] = var[0].term;
  v[1] = var[1].term;
  v[2] = var[2].term;
  v[3] = var[3].term;
  s[0] = find_map(var[0].type, 20);
  s[1] = find_map(var[1].type, 30);
  s[2] = find_map(var[2].type, 40);
  s[3] = find_map(var[3].type, 10);
  for (i=0; i<NTESTS; i++) {
    test_substitution(4, v, s, test[i]);
  }

  v[0] = unint[2].term;
  v[1] = unint[3].term;
  s[0] = find_map(unint[2].type, 14);
  s[1] = find_map(unint[3].type, 26);
  for (i=0; i<NTESTS; i++) {
    test_substitution(4, v, s, test[i]);
  }


  yices_exit();

  return 0;
}
