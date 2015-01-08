/*
 * Prettty printing a term.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include <yices.h>


/*
 * Pretty print t on stdout
 * - the pretty-printing area has width w, height h, offset 0
 */
static void pp_term(term_t t, uint32_t w, uint32_t h) {
  int32_t code;

  printf("Area: %"PRIu32" x %"PRIu32"\n", w, h);
  code = yices_pp_term(stdout, t, w, h, 0);
  if (code == OUTPUT_ERROR) {
    perror("show_term");
    exit(1);
  }
  printf("---\n");
}

/*
 * Print term t using different sizes
 */
static void test_pp(term_t t) {
  uint32_t w, h;

  w = 120;
  h = 40;
  while (w > 0) {
    pp_term(t, w, h);
    w -= 6;
    h -= 2;
  }
}


/*
 * Create the sum a + b + 1
 */
static term_t aux_sum(term_t a, term_t b) {
  term_t aux[3];

  aux[0] = a;
  aux[1] = b;
  aux[2] = yices_int32(1);
  return yices_sum(3, aux);
}


static term_t build_term(void) {
  char name[10];
  term_t x[20];
  term_t p[20];
  type_t tau;
  uint32_t i, j;

  // create 20 uinterpreted integer terms called x0 ... x19
  tau = yices_int_type();
  for (i=0; i<20; i++) {
    x[i] = yices_new_uninterpreted_term(tau);
    snprintf(name, 10, "x%"PRIu32, i);
    yices_set_term_name(x[i], name);
  }

  // build p[i] = xi + x_{i+1} + 1
  for (i=0; i<20; i++) {
    j = i+1;
    if (j >= 20) j = 0;
    p[i] = aux_sum(x[i], x[j]);
  }

  // build (and (p[0] >= 0) .... (p[19] >= 0))
  for (i=0; i<20; i++) {
    p[i] = yices_arith_geq0_atom(p[i]);
  }

  return yices_and(20, p);
}



int main(void) {
  yices_init();
  test_pp(build_term());
  yices_exit();

  return 0;
}
