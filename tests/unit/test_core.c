/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST OF SMT_CORE MODULE
 */

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "solvers/cdcl/smt_core.h"
#include "solvers/cdcl/smt_core_printer.h"


/*
 * Null theory: provide empty functions
 */
typedef struct empty_theory {
  smt_core_t *core;
  uint32_t b_level;
  uint32_t d_level;
  char *name;
} empty_theory_t;

static void null_start_internalization(void *t) {
  empty_theory_t *th;

  th = t;
  printf("%s->start_internalization\n", th->name);
  fflush(stdout);
}

static void null_start_search(void *t) {
  empty_theory_t *th;

  th = t;
  printf("%s->start_search\n", th->name);
  fflush(stdout);
}

static bool null_assert(void *t, void *atom, literal_t l) {
  empty_theory_t *th;

  th = t;
  printf("%s->assert: literal = %"PRId32"\n", th->name, l);
  fflush(stdout);

  return true;
}

static bool null_propagate(void *t) {
  empty_theory_t *th;

  th = t;
  printf("%s->propagate\n", th->name);
  fflush(stdout);

  return true;
}

static void null_expand_expl(void *t, literal_t l, void *expl, ivector_t *v) {
  assert(false);
}

static void null_increase_dlevel(void *t) {
  empty_theory_t *th;

  th = t;
  th->d_level ++;
  printf("%s->increase_dlevel: new level = %"PRIu32"\n", th->name, th->d_level);
  fflush(stdout);
}

static void null_backtrack(void *t, uint32_t back_level) {
  empty_theory_t *th;

  th = t;
  printf("%s->backtrack: old level = %"PRIu32", new level = %"PRIu32"\n", th->name,
	 th->d_level, back_level);
  th->d_level = back_level;
  fflush(stdout);
}

static void null_delete_atom(void *t, void *atom) {
  assert(false);
}

static void null_end_deletion(void *t) {
  empty_theory_t *th;

  th = t;
  printf("%s->end_deletion\n", th->name);
  fflush(stdout);
}

static void null_push(void *t) {
  empty_theory_t *th;

  th = t;
  th->b_level ++;
  th->d_level = th->b_level;
  printf("%s->push: new base level = %"PRIu32"\n", th->name, th->b_level);
}

static void null_pop(void *t) {
  empty_theory_t *th;

  th = t;
  assert(th->b_level > 0);
  th->b_level --;
  th->d_level = th->b_level;
  printf("%s->pop: new base level = %"PRIu32"\n", th->name, th->b_level);
}

static void null_reset(void *t) {
  empty_theory_t *th;

  th = t;
  printf("%s->reset\n", th->name);
  th->d_level = 0;
  th->b_level = 0;
}

static literal_t null_select_polarity(void *t, void *atom, literal_t l) {
  return l;
}

static fcheck_code_t null_final_check(void *t) {
  empty_theory_t *th;

  th = t;
  printf("%s->final_check\n", th->name);
  return FCHECK_SAT;
}

static void null_clear(void *t) {
  empty_theory_t *th;

  th = t;
  printf("%s->clear\n", th->name);
}


/*
 * Global variables: empty theory + smt_core
 */
static empty_theory_t nothing;

static th_ctrl_interface_t null_ctrl = {
  null_start_internalization,
  null_start_search,
  null_propagate,
  null_final_check,
  null_increase_dlevel,
  null_backtrack,
  null_push,
  null_pop,
  null_reset,
  null_clear,
};

static th_smt_interface_t null_smt = {
  null_assert,
  null_expand_expl,
  null_select_polarity,
  null_delete_atom,
  null_end_deletion,
};

static smt_core_t core;

int main(void) {
  literal_t l;

  // Initialize nothing
  nothing.core = &core;
  nothing.d_level = 0;
  nothing.b_level = 0;
  nothing.name = "null_theory";

  // Initialize the core
  printf("---- Init ----\n");
  init_smt_core(&core, 10, &nothing, &null_ctrl, &null_smt, SMT_MODE_INTERACTIVE);
  print_smt_core(stdout, &core);

  printf("\n---- Push ----\n");
  smt_push(&core);
  print_smt_core(stdout, &core);

  printf("\n---- Push ----\n");
  smt_push(&core);
  print_smt_core(stdout, &core);

  printf("\n---- Start search ---\n");
  start_search(&core);
  print_smt_core(stdout, &core);
  printf("\n---- Process ----\n");
  smt_process(&core);
  print_smt_core(stdout, &core);

  printf("\n---- Select literal ----\n");
  l = select_unassigned_literal(&core);
  if (l == null_literal) {
    printf("---> null_literal\n");
    end_search_sat(&core);
  } else {
    printf("---> selected ");
    print_literal(stdout, l);
    printf("\n");
  }
  print_smt_core(stdout, &core);

  printf("\n---- Clear ----\n");
  smt_clear(&core);
  print_smt_core(stdout, &core);

  printf("\n---- Reset ----\n");
  reset_smt_core(&core);
  print_smt_core(stdout, &core);

  //  printf("\n---- Pop ----\n");
  //  smt_pop(&core);
  //  print_smt_core(stdout, &core);

  //  printf("\n---- Pop ----\n");
  //  smt_pop(&core);
  //  print_smt_core(stdout, &core);

  delete_smt_core(&core);

  return 0;
}
