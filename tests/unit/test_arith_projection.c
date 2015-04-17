/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <inttypes.h>

#include "api/yices_globals.h"
#include "model/arith_projection.h"
#include "utils/memalloc.h"
#include "yices.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Print variable i (i = index in proj)
 * - this assumes that all variables have a name (in the global term table)
 */
static void print_proj_var(FILE *f, aproj_vtbl_t *vtbl, int32_t i) {
  const char *name;
  term_t x;

  assert(0 < i && i < vtbl->nvars);
  x = vtbl->term_of[i];
  name = yices_get_term_name(x);
  assert(name != NULL);
  fputs(name, f);  
}

/*
 * Print monomial q * i:
 * - first; means first monomial in a constraint
 */
static void print_proj_mono(FILE *f, aproj_vtbl_t *vtbl, rational_t *q, int32_t i, bool first) {
  bool abs_one;

  if (q_is_neg(q)) {
    abs_one = q_is_minus_one(q);
    if (first) {
      fputc('-', f);
      if (i != const_idx) {
	fputc(' ', f);
      }
    } else {
      fputs(" - ", f);
    }
  } else {
    abs_one = q_is_one(q);
    if (! first) {
      fputs(" + ", f);
    }
  }

  if (i == const_idx) {
    q_print_abs(f, q);
  } else {
    if (! abs_one) {
      q_print_abs(f, q);
      fputc('*', f);
    }
    print_proj_var(f, vtbl, i);
  }
}

static void print_proj_poly(FILE *f, aproj_vtbl_t *vtbl, monomial_t *p, uint32_t n) {
  uint32_t i;
  bool first;

  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_proj_mono(f, vtbl, &p[i].coeff, p[i].var, first);
      first = false;
    }
  }
}

static void print_proj_constraint(FILE *f, aproj_vtbl_t *vtbl, aproj_constraint_t *c) {
  print_proj_poly(f, vtbl, c->mono, c->nterms);
  switch (c->tag) {
  case APROJ_GT:
    fputs(" > 0", f);
    break;
  case APROJ_GE:
    fputs(" >= 0", f);
    break;
  case APROJ_EQ:
    fputs(" = 0", f);
    break;
  default:
    fprintf(stderr, "BUG: invalid constraint tag (%"PRId32")\n", (int32_t) c->tag);
    exit(1);
    break;
  }
}


/*
 * Print variables of index [k, ..., n-1]
 */
static void show_proj_var_array(FILE *f, aproj_vtbl_t *vtbl, uint32_t k, uint32_t n) {
  assert(0 < k && k <= n && n <= vtbl->nvars);

  if (k == n) {
    fputs("none", f);
  } else {
    fputc('[', f);
    for (;;) {
      print_proj_var(f, vtbl, k);
      k ++;
      if (k == n) break;
      fputc(' ', f);
    }
    fputc(']', f);
  }
}

static void show_proj_vars_to_elim(FILE *f, aproj_vtbl_t *vtbl) {
  show_proj_var_array(f, vtbl, 1, vtbl->nelims);
}

static void show_proj_vars_to_keep(FILE *f, aproj_vtbl_t *vtbl) {
  show_proj_var_array(f, vtbl, vtbl->nelims, vtbl->nvars);
}


/*
 * Scores of variables to eliminate
 */
static void show_proj_var_score(FILE *f, aproj_vtbl_t *vtbl, int32_t k) {
  aproj_score_t *score;

  assert(1 <= k && k < vtbl->nelims);

  score = vtbl->score + k;

  fputs("  score[", f);
  print_proj_var(f, vtbl, k);
  fprintf(f, "]: eq: %"PRIu32", pos: %"PRIu32", neg: %"PRIu32"\n",
	  score->eq_count, score->pos_count, score->neg_count);
}

static void show_scores(FILE *f, arith_projector_t *proj) {
  aproj_vtbl_t *vtbl;
  uint32_t i, n;

  vtbl = &proj->vtbl;
  n = vtbl->nelims;
  for (i=1; i<n; i++) {
    show_proj_var_score(f, vtbl, i);
  }  
}


/*
 * Values in model
 */
static void show_proj_var_value(FILE *f, aproj_vtbl_t *vtbl, int32_t k) {
  assert(1 <= k && k < vtbl->nvars);
  fputs("  value[", f);
  print_proj_var(f, vtbl, k);
  fputs("] = ", f);
  q_print(f, &vtbl->val[k]);
  fputc('\n', f);
}

static void show_values(FILE *f, arith_projector_t *proj) {
  aproj_vtbl_t *vtbl;
  uint32_t i, n;

  vtbl = &proj->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    show_proj_var_value(f, vtbl, i);
  }  
}


/*
 * All constraints in ptr_set s
 */
static void show_constraint_set(FILE *f, aproj_vtbl_t *vtbl, ptr_set2_t *s) {
  uint32_t i, n;
  aproj_constraint_t *c;

  if (s == NULL) {
    fputs("none\n", f);
  } else {
    n = s->size;
    for (i=0; i<n; i++) {
      c = s->data[i];
      if (c != NULL && c != DELETED_PTR_ELEM) {
	fputs("\n    ", f);
	print_proj_constraint(f, vtbl, c);
      }
    }
    fputc('\n', f);
  }
}

static void show_projector(FILE *f, arith_projector_t *proj) {
  fprintf(f, "Projector: %p\n", proj);
  fprintf(f, "  vars to elim: ");  
  show_proj_vars_to_elim(f, &proj->vtbl);
  fputc('\n', f);
  fprintf(f, "  vars to keep: ");
  show_proj_vars_to_keep(f, &proj->vtbl);
  fputc('\n', f);
  fprintf(f, "  constraints: ");
  show_constraint_set(f, &proj->vtbl, proj->constraints);
}


/*
 * Print and error and quit if something fails in term construction
 */
static void error_in_yices(const char *msg) {
  fprintf(stderr, "Error: %s\n", msg);
  yices_print_error(stderr);
  fflush(stderr);
  exit(1);
}


/*
 * GLOBAL TABLES
 */

/*
 * Each variable is defined by
 * - a name + a rational value given by a pair of int32: num/den
 */
typedef struct var_desc_s {
  const char *name;
  int32_t num;
  uint32_t den;
} var_desc_t;

#define NUM_VARS 10

static const var_desc_t var_desc[NUM_VARS] = {
  { "a",  0, 1 },
  { "b",  1, 1 },
  { "c", -1, 1 },
  { "d",  0, 1 },
  { "e",  1, 1 },
  { "v", -1, 1 },
  { "w",  1, 2 },
  { "x", -1, 2 },
  { "y",  2, 1 },
  { "z", -2, 3 },
};

/*
 * From the descriptors, we build two arrays:
 * - var[i] = term for variable i
 * - value[i] = rational value for i
 */
static term_t var[NUM_VARS];
static rational_t value[NUM_VARS];

/*
 * Rational constants used to build polynomials
 */
typedef struct rational_desc_s {
  int32_t num;
  uint32_t den;
} rational_desc_t;

#define NUM_CONSTANTS 9

static const rational_desc_t const_desc[NUM_CONSTANTS] = {
  {  0, 1 },
  {  1, 1 },
  { -1, 1 },
  {  1, 2 },
  { -1, 2 },
  {  2, 1 },
  { -2, 1 },
  {  3, 1 },
  { -3, 1 },
};

// same thing converted to rationals
static rational_t cnst[NUM_CONSTANTS];

/*
 * Polynomial descriptor:
 * - nterms = number of monomials
 * - size = size of arrays term/num/den
 * - term = array of terms
 * - num/den = array of integers (coef i is num[i]/den[i])
 * - c_num/c_den = constant term
 * - val = value of the polynomial
 *
 * The polynomial is defined by
 *   num[0]/den[0] * term[0] + ... + num[n-1]/den[n-1] * term[n-1]
 * where term[i] is equal to var[k] for some k.
 * The value is obtained by mapping term[i] to value[k]
 */
typedef struct poly_desc_s {
  uint32_t nterms;
  uint32_t size;
  int32_t c_num;
  uint32_t c_den;
  term_t *term;
  int32_t *num;
  uint32_t *den;
  rational_t val;
} poly_desc_t;


/*
 * Initialize/cleanup global tables
 */
static void init_globals(void) {
  uint32_t i;
  term_t x;
  type_t tau;
  int32_t code;

  tau = yices_real_type();
  for (i=0; i<NUM_VARS; i++) {
    x = yices_new_uninterpreted_term(tau);
    if (x < 0) error_in_yices("variable declaration");
    var[i] = x;
    code = yices_set_term_name(x, var_desc[i].name);
    if (code < 0) error_in_yices("set_term_name");
  }

  for (i=0; i<NUM_VARS; i++) {
    q_init(value + i);
    q_set_int32(value + i, var_desc[i].num, var_desc[i].den);
  }

  for (i=0; i<NUM_CONSTANTS; i++) {
    q_init(cnst + i);
    q_set_int32(cnst + i, const_desc[i].num, const_desc[i].den);
  }
}

static void cleanup_globals(void) {
  uint32_t i;

  for (i=0; i<NUM_VARS; i++) {
    q_clear(value + i);
  }
  for (i=0; i<NUM_CONSTANTS; i++) {
    q_clear(cnst + i);
  }
}


/*
 * Polynomial construction
 */

/*
 * Initialize p: n = size
 */
static void init_poly_desc(poly_desc_t *p, uint32_t n) {
  assert(n < UINT32_MAX/sizeof(term_t));

  p->size = n;
  p->nterms = 0;
  p->c_num = 0;
  p->c_den = 1;
  p->term = (term_t *) safe_malloc(n * sizeof(term_t));
  p->num = (int32_t *) safe_malloc(n * sizeof(int32_t));
  p->den = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  q_init(&p->val);
}

// make sure size >= n
static void resize_poly_desc(poly_desc_t *p, uint32_t n) {
  assert(n < UINT32_MAX/sizeof(term_t));

  if (p->size < n) {
    p->term = (term_t *) safe_realloc(p->term, n * sizeof(term_t));
    p->num = (int32_t *) safe_realloc(p->num, n * sizeof(int32_t));
    p->den = (uint32_t *) safe_realloc(p->den, n * sizeof(uint32_t));
  }
}

static void delete_poly_desc(poly_desc_t *p) {
  safe_free(p->term);
  safe_free(p->num);
  safe_free(p->den);
  q_clear(&p->val);
  p->term = NULL;
  p->num = NULL;
  p->den = NULL;
}

/*
 * Random boolean
 */
static bool random_bool(void) {
  return (random() & 0x8000) == 0;
}

#if 0
/*
 * Get a random rational in (num, den)
 */
static void random_constant(int32_t *num, uint32_t *den) {
  uint32_t i;

  i = random() % NUM_CONSTANTS;
  assert(i < NUM_CONSTANTS && const_desc[i].den != 0);
  *num = const_desc[i].num;
  *den = const_desc[i].den;
}
#endif

/*
 * Build a random polynomial in p
 * - p must be initialized
 * - n = number of monomials (excluding the constant)
 */
static void make_random_poly(poly_desc_t *p, uint32_t n) {
  uint32_t i, j, k;

  resize_poly_desc(p, n);
  p->nterms = n;

  k = random() % NUM_CONSTANTS; 
  p->c_num = const_desc[k].num;
  p->c_den = const_desc[k].den;
  q_set(&p->val, cnst + k);

  for (i=0; i<n; i++) {
    j = random() % NUM_VARS;
    k = random() % NUM_CONSTANTS;

    p->term[i] = var[j];
    p->num[i] = const_desc[k].num;
    p->den[i] = const_desc[k].den;

    q_addmul(&p->val, value + j, cnst + k);
  }
}

/*
 * Build term defined by p
 */
static term_t build_poly_term(poly_desc_t *p) {
  term_t c, t;

  c = yices_rational32(p->c_num, p->c_den);
  if (c < 0) error_in_yices("yices_rational32");
  t = yices_poly_rational32(p->nterms, p->num, p->den, p->term);
  if (t < 0) error_in_yices("yices_poly_rational32");
  t = yices_add(c, t);
  if (t < 0) error_in_yices("yices_add");

  return t;
}



/*
 * TESTS
 */

/*
 * Add variables in var[i .. k-1] to proj
 * - to_elim = whether to mark them as eliminate/keep variables
 */
static void test_addvars(arith_projector_t *proj, uint32_t i, uint32_t k, bool to_elim) {
  assert(i <= k && k <= NUM_VARS);

  while (i < k) {
    aproj_add_var(proj, var[i], to_elim, &value[i]);
    i ++;    
  }
}

/*
 * Given polynomial descriptor p
 * - add a constraint satistied by p
 */
static void test_add_poly_constraint(arith_projector_t *proj, poly_desc_t *p) {
  term_t t, u;
  int32_t code;

  t = build_poly_term(p);
  if (q_is_pos(&p->val)) {
    if (random_bool()) {
      u = yices_arith_gt0_atom(t);
    } else {
      u = yices_arith_geq0_atom(t);
    }
  } else if (q_is_neg(&p->val)) {
    if (random_bool()) {
      u = yices_arith_lt0_atom(t);
    } else {
      u = yices_arith_leq0_atom(t);
    }
  } else {
    u = yices_arith_eq0_atom(t);
  }

  if (u < 0) error_in_yices("arith atom");

  code = aproj_add_constraint(proj, u);

  if (code < 0) {
    fprintf(stderr, "error in test_add_poly_constraint: code = %"PRId32"\n", code);
    fflush(stderr);
    exit(1);
  }
}
 

static void test_add_bineq(arith_projector_t *proj) {
  uint32_t i, j;
  term_t u;
  int32_t code;

  i = random() % NUM_VARS;
  j = i;
  do {
    j ++;
    if (j == NUM_VARS) j = 0;
    if (q_eq(value + i, value + j)) break;
  } while (j != i);

  u = yices_arith_eq_atom(var[i], var[j]);
  if (u < 0) error_in_yices("bineq");

  code = aproj_add_constraint(proj, u);

  if (code < 0) {
    fprintf(stderr, "error in test_add_bineq: code = %"PRId32"\n", code);
    fflush(stderr);
    exit(1);
  }
}

static void test_vars(void) {
  arith_projector_t proj;
  uint32_t n;

  init_arith_projector(&proj, __yices_globals.manager, 4, 2);
  printf("*** After init ***\n");
  show_projector(stdout, &proj);  
  printf("\n");

  n = NUM_VARS;

  test_addvars(&proj, 0, n, false);
  printf("*** After addvar 0/%"PRIu32" ***\n", n);
  show_projector(stdout, &proj);
  printf("\n");

  reset_arith_projector(&proj);
  printf("*** After reset ***\n");
  show_projector(stdout, &proj);  
  printf("\n");

  test_addvars(&proj, 0, n, true);
  printf("*** After addvar %"PRIu32"/0 ***\n", n);
  show_projector(stdout, &proj);
  printf("\n");

  reset_arith_projector(&proj);
  printf("*** After reset ***\n");
  show_projector(stdout, &proj);  
  printf("\n");

  test_addvars(&proj, 5, 10, true);
  test_addvars(&proj, 0, 5, false);
  printf("*** After addvar 5/5 ***\n");
  show_projector(stdout, &proj);
  printf("\n");


  reset_arith_projector(&proj);
  printf("*** After reset ***\n");
  show_projector(stdout, &proj);  
  printf("\n");

  test_addvars(&proj, 5, 7, true);
  test_addvars(&proj, 0, 3, false);
  test_addvars(&proj, 7, 8, true);
  test_addvars(&proj, 3, 5, false);
  test_addvars(&proj, 8, 10, true);
  printf("*** After addvar 5/5 ***\n");
  show_projector(stdout, &proj);
  printf("\n");


  delete_arith_projector(&proj);
}

/*
 * Add vars and constraints
 */
static void test_constraints(void) {
  arith_projector_t proj;
  poly_desc_t p;
  uint32_t i;
  term_t t;

  init_arith_projector(&proj, __yices_globals.manager, 0, 0);
  init_poly_desc(&p, 10);
  test_addvars(&proj, 0, 5, false); // a, b, c, d, e: vars to keep
  test_addvars(&proj, 5, 10, true); // v, w, x, y, z: vars to eliminate
  aproj_close_var_set(&proj);

  for (i=0; i<20; i++) {
    make_random_poly(&p, 4);
    test_add_poly_constraint(&proj, &p);
  }
  for (i=0; i<6; i++) {
    test_add_bineq(&proj);
  }
  printf("*** After adding constraints ***\n");
  show_projector(stdout, &proj);  
  show_scores(stdout, &proj);
  show_values(stdout, &proj);
  printf("\n");
 
  aproj_eliminate(&proj);
  printf("*** After elimination ***\n");
  show_projector(stdout, &proj);  
  show_scores(stdout, &proj);
  show_values(stdout, &proj);
  printf("\n");

  t = aproj_get_formula(&proj);
  printf("*** Result formula ***\n");
  yices_pp_term(stdout, t, 120, 40, 0);
  printf("\n");

  delete_poly_desc(&p);
  delete_arith_projector(&proj);
}


int main(void) {
  uint32_t n;

  yices_init();
  init_globals();

  test_vars();
  for (n=0; n<200; n++) {
    test_constraints();
  }

  cleanup_globals();
  yices_exit();

  return 0;
}
