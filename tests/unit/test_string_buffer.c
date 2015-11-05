/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "terms/bv_constants.h"
#include "terms/rationals.h"
#include "utils/memalloc.h"
#include "utils/string_buffers.h"

static string_buffer_t buffer;

static void show_test(const char *desc, string_buffer_t *s) {
  char *content;
  uint32_t len;

  printf("%s\n", desc);
  string_buffer_append_char(s, '!');
  string_buffer_print(stdout, s);
  printf("\n");
  fflush(stdout);

  content = string_buffer_export(s, &len);
  printf("Exported to %s\n", content);
  printf("len = %"PRIu32"\n", len);
  printf("---\n");

  safe_free(content);
}

static char aux[40];

static mpz_t z0, z1;
static mpq_t q0;

static uint32_t *bv0;

int main(void) {
  int32_t x, y;
  uint32_t a, b, n;
  char c;
  string_buffer_t *s;

  s = &buffer;
  init_string_buffer(s, 0);
  show_test("empty buffer", s);

  string_buffer_reset(s);
  for (c = 'a'; c <= 'z'; c++) {
    string_buffer_append_char(s, c);
  }
  show_test("alphabet", s);

  string_buffer_reset(s);
  for (c = 'a'; c <= 'z'; c++) {
    string_buffer_append_char(s, c);
  }
  string_buffer_append_string(s, "au898ue2bcc90219");
  show_test("alphabet+au898ue2bcc90219", s);

  x = INT32_MIN;
  for (;;){
    sprintf(aux, "signed number: %" PRId32, x);
    string_buffer_reset(s);
    string_buffer_append_int32(s, x);
    show_test(aux, s);
    y = x >> 1;
    if (y == x) break;
    x = y;
  }

  x = INT32_MAX;
  for (;;) {
    sprintf(aux, "signed number: %" PRId32, x);
    string_buffer_reset(s);
    string_buffer_append_int32(s, x);
    show_test(aux, s);
    y = x>>1;
    if (y == x) break;
    x = y;
  }

  a = UINT32_MAX;
  for (;;){
    sprintf(aux, "unsigned number: %" PRIu32, a);
    string_buffer_reset(s);
    string_buffer_append_uint32(s, a);
    show_test(aux, s);
    b = a >> 1;
    if (b == a) break;
    a = b;
  }

  mpz_init(z0);
  mpz_init(z1);
  mpq_init(q0);

  mpz_set_str(z0, "111102222033330123456789", 10);
  string_buffer_reset(s);
  string_buffer_append_mpz(s, z0);
  show_test("mpz: 111102222033330123456789", s);

  mpz_set_str(z0, "-111102222033330123456789", 10);
  string_buffer_reset(s);
  string_buffer_append_mpz(s, z0);
  show_test("mpz: -111102222033330123456789", s);

  string_buffer_reset(s);
  string_buffer_append_mpz(s, z1);
  show_test("mpz: 0", s);

  mpq_set_str(q0, "-98765432109876543210", 10);
  string_buffer_reset(s);
  string_buffer_append_mpq(s, q0);
  show_test("mpq: -98765432109876543210", s);

  mpq_set_str(q0, "-98765432109876543210/38192839777", 10);
  string_buffer_reset(s);
  string_buffer_append_mpq(s, q0);
  show_test("mpq: -98765432109876543210/38192839777", s);

  init_rationals();
  rational_t r0;
  q_init(&r0);
  string_buffer_reset(s);
  string_buffer_append_rational(s, &r0);
  show_test("rational: 0", s);

  q_set_int32(&r0, -12, 73);
  string_buffer_reset(s);
  string_buffer_append_rational(s, &r0);
  show_test("rational: -12/73", s);

  q_set_mpq(&r0, q0);
  string_buffer_reset(s);
  string_buffer_append_rational(s, &r0);
  show_test("rational: -98765432109876543210/38192839777", s);

  q_set_mpz(&r0, z0);
  string_buffer_reset(s);
  string_buffer_append_rational(s, &r0);
  show_test("rational: -111102222033330123456789", s);


  printf("\nBit Vectors\n");
  init_bvconstants();
  bv0 = bvconst_alloc(1);
  bvconst_clear(bv0, 1);
  for (n=1; n<= 32; n++) {
    string_buffer_reset(s);
    string_buffer_append_bvconst(s, bv0, n);
    sprintf(aux, "bv[%" PRIu32"]: 0b000...", n);
    show_test(aux, s);
  }

  for (n=1; n <= 32; n++) {
    bvconst_clear(bv0, 1);
    bvconst_set_bit(bv0, n-1);
    string_buffer_reset(s);
    string_buffer_append_bvconst(s, bv0, n);
    sprintf(aux, "bv[%" PRIu32"]: 0b100...", n);
    show_test(aux, s);
  }


  bvconst_free(bv0, 1);

  cleanup_bvconstants();

  cleanup_rationals();

  mpz_clear(z0);
  mpz_clear(z1);
  mpq_clear(q0);

  delete_string_buffer(s);

  return 0;
}
