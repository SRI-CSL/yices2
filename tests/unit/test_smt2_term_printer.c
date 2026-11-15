/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Test the SMT-LIB 2 term printer (issue #686).
 *
 * Terms are built with the API then printed with smt2_pp_term. The output is
 * compared with the expected SMT-LIB 2 text. The program exits with a
 * non-zero code if a comparison fails.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "api/yices_globals.h"
#include "frontend/smt2/smt2_term_printer.h"
#include "yices.h"


static int failures = 0;

/*
 * Print t in a string (one line). Return false if smt2_pp_term refuses t.
 */
static bool print_term(term_t t, char *buf, size_t size) {
  smt2_pp_t printer;
  pp_area_t area;
  FILE *f;
  size_t n;
  bool ok;

  f = tmpfile();
  if (f == NULL) {
    fprintf(stderr, "tmpfile failed\n");
    exit(2);
  }
  area.width = 100000;
  area.height = 100;
  area.offset = 0;
  area.stretch = false;
  area.truncate = false;
  init_smt2_pp(&printer, f, &area, PP_VMODE, false);
  ok = smt2_pp_term(&printer, __yices_globals.terms, t);
  delete_smt2_pp(&printer, ok);

  rewind(f);
  n = fread(buf, 1, size - 1, f);
  buf[n] = '\0';
  fclose(f);

  // remove the trailing newline
  while (n > 0 && (buf[n-1] == '\n' || buf[n-1] == ' ')) {
    buf[--n] = '\0';
  }

  return ok;
}

static void check(const char *name, term_t t, const char *expected) {
  char buf[4096];
  bool ok;

  ok = print_term(t, buf, sizeof(buf));
  if (expected == NULL) {
    if (ok || buf[0] != '\0') {
      printf("FAIL %s: expected a refusal, got '%s'\n", name, buf);
      failures ++;
    } else {
      printf("ok   %s: refused\n", name);
    }
  } else if (!ok || strcmp(buf, expected) != 0) {
    printf("FAIL %s:\n  expected: %s\n  got:      %s\n", name, expected, ok ? buf : "<refused>");
    failures ++;
  } else {
    printf("ok   %s: %s\n", name, buf);
  }
}

static term_t var(const char *name, type_t tau) {
  term_t x = yices_new_uninterpreted_term(tau);
  yices_set_term_name(x, name);
  return x;
}


int main(void) {
  type_t bool_t, int_t, real_t, bv8, bv70, f_t;
  term_t b, c, i, j, r, s, x, y, z, w, f, q;
  term_t t, u;

  yices_init();

  bool_t = yices_bool_type();
  int_t = yices_int_type();
  real_t = yices_real_type();
  bv8 = yices_bv_type(8);
  bv70 = yices_bv_type(70);
  f_t = yices_function_type1(int_t, int_t);

  b = var("b", bool_t);
  c = var("c", bool_t);
  i = var("i", int_t);
  j = var("j", int_t);
  r = var("r", real_t);
  s = var("s", real_t);
  x = var("x", bv8);
  y = var("y", bv8);
  z = var("z", bv70);
  w = var("a weird name", bool_t);
  f = var("f", f_t);

  // the example of issue #686
  t = yices_bvslt_atom(yices_bvadd(yices_bvadd(x, y), y), yices_bvconst_zero(8));
  check("issue686", t, "(bvslt (bvadd x (bvmul #b00000010 y)) #b00000000)");

  // Boolean
  check("true", yices_true(), "true");
  check("false", yices_false(), "false");
  check("not b", yices_not(b), "(not b)");
  check("or", yices_or2(b, yices_not(c)), "(or b (not c))");
  check("xor", yices_xor(3, (term_t[]) { b, c, w }), "(xor b c |a weird name|)");
  check("not xor", yices_not(yices_xor(3, (term_t[]) { b, c, w })), "(not (xor b c |a weird name|))");
  check("iff", yices_iff(b, c), "(= b c)");
  check("not iff", yices_not(yices_iff(b, c)), "(not (= b c))");
  check("quoted symbol", w, "|a weird name|");
  check("ite", yices_ite(b, c, w), "(ite b c |a weird name|)");

  // UF
  check("app", yices_application1(f, i), "(f i)");
  check("eq app", yices_eq(yices_application1(f, i), j), "(= j (f i))");
  check("neq", yices_neq(i, j), "(distinct i j)");
  check("distinct", yices_distinct(3, (term_t[]) { i, j, yices_int32(3) }), "(distinct i j 3)");

  // Arithmetic
  t = yices_arith_geq0_atom(yices_sub(yices_mul(yices_int32(3), i), j));
  check("ge0", t, "(>= (+ (* 3 i) (* (- 1) j)) 0)");
  check("lt0", yices_not(t), "(< (+ (* 3 i) (* (- 1) j)) 0)");
  check("arith eq0", yices_arith_eq0_atom(yices_sub(i, yices_int32(5))), "(= i 5)");
  check("arith neq0", yices_not(yices_arith_eq0_atom(yices_sub(i, yices_int32(5)))), "(distinct i 5)");
  check("negative constant", yices_arith_eq_atom(i, yices_int32(-7)), "(= i (- 7))");
  check("real poly", yices_arith_geq0_atom(yices_sub(yices_mul(yices_int32(2), r), s)), "(>= (+ (* 2.0 r) (* (- 1.0) s)) 0.0)");
  check("rational", yices_arith_leq_atom(r, yices_rational32(-5, 4)), "(>= (+ (/ (- 5.0) 4.0) (* (- 1.0) r)) 0.0)");
  check("power", yices_arith_eq_atom(yices_power(i, 3), yices_int32(8)), "(= (* i i i) 8)");
  check("product", yices_arith_eq_atom(yices_mul(i, j), yices_int32(8)), "(= 8 (* i j))");
  check("div", yices_arith_eq_atom(yices_idiv(i, j), yices_int32(1)), "(= (div i j) 1)");
  check("mod", yices_arith_eq_atom(yices_imod(i, j), yices_int32(1)), "(= 1 (mod i j))");
  check("rdiv", yices_arith_eq_atom(yices_division(r, s), yices_int32(1)), "(= 1.0 (/ r s))");
  check("divides const", yices_divides_atom(yices_int32(3), i), "((_ divisible 3) i)");
  check("not divides const", yices_not(yices_divides_atom(yices_int32(3), i)), "(not ((_ divisible 3) i))");
  check("floor", yices_arith_eq_atom(yices_floor(r), i), "(= i (to_int r))");
  check("ceil", yices_arith_eq_atom(yices_ceil(r), i), "(= i (- (to_int (- r))))");
  check("is_int", yices_is_int_atom(r), "(is_int r)");
  check("abs", yices_arith_eq_atom(yices_abs(i), j), "(= j (ite (>= i 0) i (- i)))");

  // Bit-vectors
  check("bv const", yices_eq(x, yices_bvconst_uint32(8, 5)), "(= x #b00000101)");
  check("bvuge", yices_bvge_atom(x, y), "(bvuge x y)");
  check("bvult", yices_not(yices_bvge_atom(x, y)), "(bvult x y)");
  check("bvsge", yices_bvsge_atom(x, y), "(bvsge x y)");
  check("bvslt", yices_bvslt_atom(x, y), "(bvslt x y)");
  check("bvadd", yices_eq(yices_bvadd(x, y), yices_bvconst_uint32(8, 1)), "(= (bvadd x y) #b00000001)");
  check("bvmul", yices_eq(yices_bvmul(x, y), yices_bvconst_uint32(8, 1)), "(= #b00000001 (bvmul x y))");
  check("bvudiv", yices_eq(yices_bvdiv(x, y), x), "(= x (bvudiv x y))");
  check("bvurem", yices_eq(yices_bvrem(x, y), x), "(= x (bvurem x y))");
  check("bvsdiv", yices_eq(yices_bvsdiv(x, y), x), "(= x (bvsdiv x y))");
  check("bvsrem", yices_eq(yices_bvsrem(x, y), x), "(= x (bvsrem x y))");
  check("bvsmod", yices_eq(yices_bvsmod(x, y), x), "(= x (bvsmod x y))");
  check("bvshl", yices_eq(yices_bvshl(x, y), x), "(= x (bvshl x y))");
  check("bvlshr", yices_eq(yices_bvlshr(x, y), x), "(= x (bvlshr x y))");
  check("bvashr", yices_eq(yices_bvashr(x, y), x), "(= x (bvashr x y))");
  check("extract", yices_eq(yices_bvextract(x, 0, 3), yices_bvconst_uint32(4, 6)), "(= ((_ extract 3 0) x) #b0110)");
  check("concat", yices_eq(yices_bvconcat2(x, y), yices_bvconst_uint32(16, 6)), "(= (concat x y) #b0000000000000110)");
  check("bit", yices_bitextract(x, 6), "(= ((_ extract 6 6) x) #b1)");
  check("not bit", yices_not(yices_bitextract(x, 6)), "(not (= ((_ extract 6 6) x) #b1))");
  check("bit vector from bools", yices_eq(yices_bvarray(3, (term_t[]) { b, yices_true(), yices_not(c) }), yices_bvconst_uint32(3, 2)),
	"(= (concat (ite (not c) #b1 #b0) #b1 (ite b #b1 #b0)) #b010)");
  // a negated bit must not be mistaken for the bit itself when slicing
  check("negated bit in array",
	yices_eq(yices_bvarray(2, (term_t[]) { yices_not(yices_bitextract(x, 2)), yices_bitextract(x, 3) }), yices_bvconst_uint32(2, 1)),
	"(= (concat ((_ extract 3 3) x) (ite (not (= ((_ extract 2 2) x) #b1)) #b1 #b0)) #b01)");
  check("wide constant", yices_eq(z, yices_bvconst_minus_one(70)), "(= z #b1111111111111111111111111111111111111111111111111111111111111111111111)");
  u = yices_eq(yices_bvadd(z, yices_bvconst_one(70)), yices_bvconst_zero(70));
  check("wide bvadd", u, "(= (bvadd #b0000000000000000000000000000000000000000000000000000000000000000000001 z) #b0000000000000000000000000000000000000000000000000000000000000000000000)");

  // Terms that cannot be printed
  q = yices_new_variable(int_t);
  check("forall", yices_forall(1, &q, yices_arith_geq0_atom(q)), NULL);
  check("lambda", yices_eq(yices_lambda(1, &q, q), f), NULL);
  check("tuple", yices_eq(yices_tuple(2, (term_t[]) { i, j }), yices_tuple(2, (term_t[]) { j, i })), NULL);
  check("update", yices_eq(yices_update1(f, i, j), f), NULL);

  yices_exit();

  if (failures > 0) {
    printf("%d failures\n", failures);
    return 1;
  }
  printf("All tests passed\n");
  return 0;
}
