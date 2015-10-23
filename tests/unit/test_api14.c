/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST OUT-OF-MEM CALLBACK
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <setjmp.h>

#include "yices.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif

// create an arithmetic constant (integer between -200 and +200)
static term_t make_arith_constant(void) {
  int32_t x;

  x = (random() % 402) - 200;
  return yices_int32(x);
}

/*
 * create two uninterperted terms x<i> and y<i> and combine them
 * using an arithmetic operation.
 */
static term_t make_a_term(uint32_t i) {
  char name[40];
  type_t tau;
  term_t x, y, z, t;

  tau = yices_real_type();

  x = yices_new_uninterpreted_term(tau);
  sprintf(name, "x%"PRIu32, i);
  yices_set_term_name(x, name);

  y = yices_new_uninterpreted_term(tau);
  sprintf(name, "y%"PRIu32, i);
  yices_set_term_name(y, name);

  z = make_arith_constant();

  switch (i % 8) {
  case 0:
    t = yices_add(yices_add(x, y), z);
    break;

  case 1:
    t = yices_add(yices_sub(x, y), z);
    break;

  case 2:
    t = yices_mul(yices_add(x, y), z);
    break;

  case 3:
    t = yices_mul(yices_sub(x, y), z);
    break;

  case 4:
    t = yices_arith_eq_atom(yices_sub(x, y), z);
    break;

  case 5:
    t = yices_arith_geq_atom(yices_mul(x, y), z);
    break;

  case 6:
    t = yices_arith_gt_atom(yices_add(x, y), z);
    break;

  case 7:
    t = yices_arith_lt0_atom(yices_mul(yices_add(x, z), y));
    break;
  }

  return t;
}


/*
 * Out-of-memory handling using setjmp/longjmp
 */
static jmp_buf *env;

static void oom_handler(void) {
  if (env == NULL) {
    fprintf(stderr, "Out of memory (uncaught)\n");
    exit(1);
  }
  longjmp(*env, -1);
}

int main(void) {
  jmp_buf buffer;
  volatile uint32_t n;
  term_t t;

  env = NULL;
  yices_set_out_of_mem_callback(oom_handler);

  if (setjmp(buffer) == 0) {
    env = &buffer;

    yices_init();  
    n = 0;
    for (;;) {
      t = make_a_term(n);
      printf("term[%"PRIu32"]: ", n);
      yices_pp_term(stdout, t, 120, 10, 0);
      n ++;
    }

    yices_exit();

  } else {
    // out-of-memory exception caught here
    fprintf(stderr, "Out of memory caught after %"PRIu32" iterations\n", n);
  }

  return 0;
}
