#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#include "yices.h"
#include "mcsat/cdclt/cdclt_sat_cache.h"

#define T0  0
#define T1  1
#define T2  2
#define T3  3

static void test_register_and_build(void) {
  cdclt_sat_cache_t c;
  cdclt_sat_cache_init(&c);
  assert(cdclt_sat_cache_register_atom(&c, T0) == 0);
  assert(cdclt_sat_cache_register_atom(&c, T1) == 1);
  assert(cdclt_sat_cache_register_atom(&c, T0) == 0);
  assert(c.n_atoms == 2);
  assert(c.n_words == 1);
  ivector_t assump;
  init_ivector(&assump, 0);
  ivector_push(&assump, T0);
  ivector_push(&assump, T1);
  assert(cdclt_sat_cache_build(&c, &assump));
  assert(c.scratch[0] == 0x3ULL);
  delete_ivector(&assump);
  cdclt_sat_cache_destroy(&c);
  printf("PASS: test_register_and_build\n");
}

static void test_sat_lookup(void) {
  cdclt_sat_cache_t c;
  cdclt_sat_cache_init(&c);
  cdclt_sat_cache_register_atom(&c, T0);
  cdclt_sat_cache_register_atom(&c, T1);
  cdclt_sat_cache_register_atom(&c, T2);
  ivector_t s;
  init_ivector(&s, 0);
  ivector_push(&s, T0); ivector_push(&s, T1); ivector_push(&s, T2);
  cdclt_sat_cache_build(&c, &s);
  cdclt_sat_cache_record_sat(&c, c.scratch);
  ivector_t q;
  init_ivector(&q, 0);
  ivector_push(&q, T0); ivector_push(&q, T1);
  cdclt_sat_cache_build(&c, &q);
  assert(cdclt_sat_cache_lookup_sat(&c, c.scratch));
  cdclt_sat_cache_build(&c, &s);
  assert(cdclt_sat_cache_lookup_sat(&c, c.scratch));
  ivector_reset(&q);
  cdclt_sat_cache_build(&c, &q);
  assert(cdclt_sat_cache_lookup_sat(&c, c.scratch));
  cdclt_sat_cache_register_atom(&c, T3);
  ivector_reset(&q);
  ivector_push(&q, T3);
  cdclt_sat_cache_build(&c, &q);
  assert(!cdclt_sat_cache_lookup_sat(&c, c.scratch));
  delete_ivector(&s);
  delete_ivector(&q);
  cdclt_sat_cache_destroy(&c);
  printf("PASS: test_sat_lookup\n");
}

static void test_unsat_lookup(void) {
  cdclt_sat_cache_t c;
  cdclt_sat_cache_init(&c);
  cdclt_sat_cache_register_atom(&c, T0);
  cdclt_sat_cache_register_atom(&c, T1);
  cdclt_sat_cache_register_atom(&c, T2);
  ivector_t core;
  init_ivector(&core, 0);
  ivector_push(&core, T0); ivector_push(&core, T1);
  cdclt_sat_cache_build(&c, &core);
  cdclt_sat_cache_record_unsat(&c, c.scratch);
  ivector_t q;
  init_ivector(&q, 0);
  ivector_push(&q, T0); ivector_push(&q, T1); ivector_push(&q, T2);
  cdclt_sat_cache_build(&c, &q);
  ivector_t conflict;
  init_ivector(&conflict, 0);
  assert(cdclt_sat_cache_lookup_unsat(&c, c.scratch, &conflict));
  assert(conflict.size == 2);
  ivector_reset(&q);
  ivector_push(&q, T0);
  cdclt_sat_cache_build(&c, &q);
  ivector_reset(&conflict);
  assert(!cdclt_sat_cache_lookup_unsat(&c, c.scratch, &conflict));
  delete_ivector(&core);
  delete_ivector(&q);
  delete_ivector(&conflict);
  cdclt_sat_cache_destroy(&c);
  printf("PASS: test_unsat_lookup\n");
}

static void test_word_boundary_resize(void) {
  cdclt_sat_cache_t c;
  cdclt_sat_cache_init(&c);

  /* Register 64 atoms (indices 0..63): all fit in 1 word */
  for (int i = 0; i < 64; i++)
    cdclt_sat_cache_register_atom(&c, (term_t)i);
  assert(c.n_words == 1);

  /* Record SAT for all 64 */
  ivector_t s;
  init_ivector(&s, 0);
  for (int i = 0; i < 64; i++) ivector_push(&s, (term_t)i);
  cdclt_sat_cache_build(&c, &s);
  cdclt_sat_cache_record_sat(&c, c.scratch);
  assert(c.sat_count == 1);

  /* Register atom 64 (index 64, n_atoms=65) -> triggers resize to 2 words */
  cdclt_sat_cache_register_atom(&c, (term_t)64);
  assert(c.n_words == 2);
  assert(c.sat_count == 1); /* existing entry still valid */

  /* Subset of cached entry should still hit */
  ivector_t q;
  init_ivector(&q, 0);
  for (int i = 0; i < 10; i++) ivector_push(&q, (term_t)i);
  cdclt_sat_cache_build(&c, &q);
  assert(cdclt_sat_cache_lookup_sat(&c, c.scratch));

  /* Adding atom 64 (not in cached S) -> no hit */
  ivector_push(&q, (term_t)64);
  cdclt_sat_cache_build(&c, &q);
  assert(!cdclt_sat_cache_lookup_sat(&c, c.scratch));

  delete_ivector(&s);
  delete_ivector(&q);
  cdclt_sat_cache_destroy(&c);
  printf("PASS: test_word_boundary_resize\n");
}

int main(void) {
  yices_init();
  test_register_and_build();
  test_sat_lookup();
  test_unsat_lookup();
  test_word_boundary_resize();
  yices_exit();
  printf("ALL PASS\n");
  return 0;
}
