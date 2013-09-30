/*
 * TEST TERM SUBSTITUTIONS
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#include "yices.h"

/*
 * Arrays of terms for testing: we store term + its type
 * - unint[i] = uninterpreted term
 * - var[i] = variable
 * - range = array of terms: all substitutions are maps from
 *   elements of unint and var to elements of range
 */
typedef struct typed_term_s {
  term_t term;
  type_t type;
} typed_term_t;

#define BASE_TYPES 5
#define NUNINTS 10
#define NVARS   10
#define NTESTS  50

static type_t base_type[BASE_TYPES];
static typed_term_t unint[NUNINTS];
static typed_term_t var[NVARS];
static typed_term_t range[NTESTS];


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

  for (i=0; i<NVARS; i++) {
    range[i] = var[i];
  }
  for (i=0; i<NUNINTS; i++) {
    range[i + NVARS] = unint[i];
  }

  i = 20;
  range[i].term = yices_int32(0);
  range[i].type = yices_int_type();
  i ++;
  range[i].term = yices_int32(1);
  range[i].type = yices_int_type();
  i++;
  range[i].term = yices_int32(-2);
  range[i].type = yices_int_type();
  i ++;
  range[i].term = yices_rational32(1, 2);
  range[i].type = yices_real_type();
  i ++;
  range[i].term = yices_rational32(-3, 2);
  range[i].type = yices_real_type();
  i ++;
  range[i].term = yices_true();
  range[i].type = yices_bool_type();
  i ++;
  range[i].term = yices_false();
  range[i].type = yices_bool_type();
  i ++;

  range[i].term = yices_bvconst_uint32(32, 0);
  range[i].type = yices_bv_type(32);
  i ++;
  range[i].term = yices_bvconst_uint32(32, 0x55555555u);
  range[i].type = yices_bv_type(32);
  i ++;
  range[i].term = yices_bvconst_uint32(32, 0x80000000u);
  range[i].type = yices_bv_type(32);
  i ++;

  range[i].term = yices_constant(base_type[4], 0);
  range[i].type = base_type[4];
  i++;
  range[i].term = yices_constant(base_type[4], 1);
  range[i].type = base_type[4];
  i++;
  
  
}

int main(void) {
  yices_init();
  init_domain();
  init_range();

  yices_exit();

  return 0;
}
