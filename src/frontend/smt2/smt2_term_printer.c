/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * PRINT TERMS IN SMT-LIB 2 SYNTAX
 */

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "frontend/smt2/smt2_symbol_printer.h"
#include "frontend/smt2/smt2_term_printer.h"
#include "terms/bv_slices.h"
#include "terms/bv64_constants.h"
#include "terms/power_products.h"
#include "terms/rationals.h"


/*
 * The printing is done in two passes: a dry run, with no output, to check
 * that every subterm is supported, then the real pass.
 */
typedef struct smt2_term_pp_s {
  smt2_pp_t *printer;
  term_table_t *tbl;
  bool dry;      // dry run: don't print anything
  bool failed;   // set when an unsupported term is found
} smt2_term_pp_t;


/*
 * Output primitives (no-ops in a dry run)
 */
static void open_op(smt2_term_pp_t *c, const char *op) {
  if (!c->dry) {
    pp_open_block(&c->printer->pp, PP_OPEN_PAR);
    pp_string(&c->printer->pp, op);
  }
}

// open a parenthesis with no operator
static void open_par(smt2_term_pp_t *c) {
  if (!c->dry) {
    pp_open_block(&c->printer->pp, PP_OPEN_PAR);
  }
}

static void close_op(smt2_term_pp_t *c) {
  if (!c->dry) {
    pp_close_block(&c->printer->pp, true);
  }
}

static void put_string(smt2_term_pp_t *c, const char *s) {
  if (!c->dry) {
    pp_string(&c->printer->pp, s);
  }
}

// ((_ name n) ... : open the application and the indexed operator
static void open_indexed_op(smt2_term_pp_t *c, const char *name, uint32_t i, uint32_t j, bool two_indices) {
  if (!c->dry) {
    pp_open_block(&c->printer->pp, PP_OPEN_PAR);
    pp_open_block(&c->printer->pp, PP_OPEN_PAR);
    pp_string(&c->printer->pp, "_");
    pp_string(&c->printer->pp, name);
    pp_uint32(&c->printer->pp, i);
    if (two_indices) {
      pp_uint32(&c->printer->pp, j);
    }
    pp_close_block(&c->printer->pp, true);
  }
}

static void fail(smt2_term_pp_t *c) {
  c->failed = true;
}

// open (not ... if polarity is false
static void open_neg(smt2_term_pp_t *c, bool polarity) {
  if (!polarity) open_op(c, "not");
}

static void close_neg(smt2_term_pp_t *c, bool polarity) {
  if (!polarity) close_op(c);
}


/*
 * Constants
 */

// bit-vector constant made of n copies of bit b ('0' or '1')
static void put_bit_run(smt2_term_pp_t *c, char b, uint32_t n) {
  char *s;

  if (c->dry) return;

  s = (char *) malloc(n + 3);
  if (s == NULL) {
    fail(c);
    return;
  }
  s[0] = '#';
  s[1] = 'b';
  memset(s + 2, b, n);
  s[n + 2] = '\0';
  pp_clone_string(&c->printer->pp, s);
  free(s);
}

// non-negative integer n: as 12 or as 12.0
static void put_natural(smt2_term_pp_t *c, rational_t *n, bool as_real) {
  if (as_real) {
    pp_smt2_integer_as_real(&c->printer->pp, n);
  } else {
    pp_rational(&c->printer->pp, n);
  }
}

// integer n (possibly negative): as 12, (- 12), 12.0, or (- 12.0)
static void put_integer(smt2_term_pp_t *c, rational_t *n, bool as_real) {
  if (q_is_neg(n)) {
    q_neg(n);
    open_op(c, "-");
    put_natural(c, n, as_real);
    close_op(c);
  } else {
    put_natural(c, n, as_real);
  }
}

// integer or rational constant: as_real is true for terms of type real
// - rationals are printed as (/ n d)
static void put_rational(smt2_term_pp_t *c, const rational_t *q, bool as_real) {
  rational_t num, den;

  if (c->dry) return;

  q_init(&num);
  q_init(&den);
  q_get_num(&num, q);
  q_get_den(&den, q);
  assert(q_is_pos(&den));

  if (q_is_one(&den)) {
    put_integer(c, &num, as_real);
  } else {
    open_op(c, "/");
    put_integer(c, &num, as_real);
    put_natural(c, &den, as_real);
    close_op(c);
  }

  q_clear(&num);
  q_clear(&den);
}

static void put_zero(smt2_term_pp_t *c, bool as_real) {
  if (!c->dry) {
    if (as_real) {
      pp_string(&c->printer->pp, "0.0");
    } else {
      pp_string(&c->printer->pp, "0");
    }
  }
}

static void put_name(smt2_term_pp_t *c, int32_t i) {
  const char *name;

  if (!c->dry) {
    name = term_name(c->tbl, pos_term(i));
    if (name != NULL) {
      smt2_pp_symbol(c->printer, name);
    } else {
      pp_id(&c->printer->pp, "t!", i);
    }
  }
}

// 1-bit vector for a Boolean
static void put_bit_const(smt2_term_pp_t *c, bool v) {
  put_string(c, v ? "#b1" : "#b0");
}


static void pp_rec(smt2_term_pp_t *c, term_t t);

// is t an arithmetic term of type real?
static bool real_syntax(smt2_term_pp_t *c, term_t t) {
  return !is_integer_term(c->tbl, t);
}

// is t an arithmetic term that is not an integer one?
static bool is_real_valued(smt2_term_pp_t *c, term_t t) {
  return is_arithmetic_term(c->tbl, t) && !is_integer_term(c->tbl, t);
}

// Argument of an arithmetic operator.
// - Yices gives type int to constants such as 1, even in a real context.
//   If as_real is true, we print these constants as reals.
static void pp_arith_arg(smt2_term_pp_t *c, term_t t, bool as_real) {
  if (as_real && is_pos_term(t) && term_kind(c->tbl, t) == ARITH_CONSTANT) {
    put_rational(c, rational_term_desc(c->tbl, t), true);
  } else {
    pp_rec(c, t);
  }
}

// (op arg[0] ... arg[n-1])
static void pp_nary(smt2_term_pp_t *c, const char *op, const term_t *arg, uint32_t n) {
  uint32_t i;

  open_op(c, op);
  for (i=0; i<n; i++) {
    pp_rec(c, arg[i]);
  }
  close_op(c);
}

// (op x 0) where x is an arithmetic term
static void pp_vs_zero(smt2_term_pp_t *c, const char *op, term_t x) {
  open_op(c, op);
  pp_rec(c, x);
  put_zero(c, real_syntax(c, x));
  close_op(c);
}


/*
 * Power products: x_1^d_1 ... x_n^d_n is a list of factors, where
 * each x_i is repeated d_i times.
 * - mul is the name of the product operator
 */
static void pp_factors(smt2_term_pp_t *c, pprod_t *p) {
  uint32_t i, j;

  for (i=0; i<p->len; i++) {
    for (j=0; j<p->prod[i].exp; j++) {
      pp_rec(c, p->prod[i].var);
    }
  }
}

static uint32_t num_factors(pprod_t *p) {
  uint32_t i, n;

  n = 0;
  for (i=0; i<p->len; i++) {
    n += p->prod[i].exp;
  }
  return n;
}

static void pp_pprod(smt2_term_pp_t *c, pprod_t *p) {
  const char *mul;
  uint32_t n;

  assert(p->len > 0);
  mul = is_bitvector_term(c->tbl, p->prod[0].var) ? "bvmul" : "*";
  n = num_factors(p);
  if (n == 1) {
    pp_rec(c, p->prod[0].var);
  } else {
    open_op(c, mul);
    pp_factors(c, p);
    close_op(c);
  }
}

// factors of x if x is a power product, otherwise x itself
static void pp_mono_factors(smt2_term_pp_t *c, int32_t x) {
  if (term_kind(c->tbl, x) == POWER_PRODUCT) {
    pp_factors(c, pprod_term_desc(c->tbl, x));
  } else {
    pp_rec(c, x);
  }
}


/*
 * Arithmetic polynomials
 */
static void pp_mono(smt2_term_pp_t *c, const rational_t *coeff, int32_t x, bool as_real) {
  if (x == const_idx) {
    put_rational(c, coeff, as_real);
  } else if (q_is_one(coeff)) {
    pp_rec(c, x);
  } else {
    open_op(c, "*");
    put_rational(c, coeff, as_real);
    pp_mono_factors(c, x);
    close_op(c);
  }
}

static void pp_poly(smt2_term_pp_t *c, polynomial_t *p, bool as_real) {
  uint32_t i, n;

  n = p->nterms;
  if (n == 1) {
    pp_mono(c, &p->mono[0].coeff, p->mono[0].var, as_real);
  } else {
    open_op(c, "+");
    for (i=0; i<n; i++) {
      pp_mono(c, &p->mono[i].coeff, p->mono[i].var, as_real);
    }
    close_op(c);
  }
}


/*
 * Bit-vector polynomials
 */
static void pp_bvmono64(smt2_term_pp_t *c, uint64_t coeff, uint32_t nbits, int32_t x) {
  if (x == const_idx) {
    if (!c->dry) pp_smt2_bv64(&c->printer->pp, coeff, nbits);
  } else if (coeff == 1) {
    pp_rec(c, x);
  } else {
    open_op(c, "bvmul");
    if (!c->dry) pp_smt2_bv64(&c->printer->pp, coeff, nbits);
    pp_mono_factors(c, x);
    close_op(c);
  }
}

static void pp_bvpoly64(smt2_term_pp_t *c, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  if (n == 1) {
    pp_bvmono64(c, p->mono[0].coeff, p->bitsize, p->mono[0].var);
  } else {
    open_op(c, "bvadd");
    for (i=0; i<n; i++) {
      pp_bvmono64(c, p->mono[i].coeff, p->bitsize, p->mono[i].var);
    }
    close_op(c);
  }
}

static void pp_bvmono(smt2_term_pp_t *c, uint32_t *coeff, uint32_t nbits, int32_t x) {
  if (x == const_idx) {
    if (!c->dry) pp_smt2_bv(&c->printer->pp, coeff, nbits);
  } else if (bvconst_is_one(coeff, (nbits + 31) >> 5)) {
    pp_rec(c, x);
  } else {
    open_op(c, "bvmul");
    if (!c->dry) pp_smt2_bv(&c->printer->pp, coeff, nbits);
    pp_mono_factors(c, x);
    close_op(c);
  }
}

static void pp_bvpoly(smt2_term_pp_t *c, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  if (n == 1) {
    pp_bvmono(c, p->mono[0].coeff, p->bitsize, p->mono[0].var);
  } else {
    open_op(c, "bvadd");
    for (i=0; i<n; i++) {
      pp_bvmono(c, p->mono[i].coeff, p->bitsize, p->mono[i].var);
    }
    close_op(c);
  }
}


/*
 * Bit-vector arrays. Bit 0 of the array is the least significant bit,
 * but concat takes the most significant piece first.
 */

// one bit b as a bit-vector of size 1
static void pp_bit_piece(smt2_term_pp_t *c, term_t b) {
  int32_t i;
  select_term_t *s;

  if (b == true_term) {
    put_bit_const(c, true);
  } else if (b == false_term) {
    put_bit_const(c, false);
  } else if (is_pos_term(b) && term_kind(c->tbl, b) == BIT_TERM) {
    // ((_ extract i i) x)
    s = bit_term_desc(c->tbl, b);
    i = s->idx;
    open_indexed_op(c, "extract", i, i, true);
    pp_rec(c, s->arg);
    close_op(c);
  } else {
    open_op(c, "ite");
    pp_rec(c, b);
    put_bit_const(c, true);
    put_bit_const(c, false);
    close_op(c);
  }
}

static void pp_bv_slice(smt2_term_pp_t *c, bvslice_t *d) {
  uint32_t i, k;
  term_t u;

  switch (d->tag) {
  case BVSLICE_REPEAT:
    u = d->desc.r.bit;
    k = d->desc.r.count;
    assert(k > 0);
    if (u == false_term) {
      put_bit_run(c, '0', k);
    } else if (u == true_term) {
      put_bit_run(c, '1', k);
    } else if (k == 1) {
      pp_bit_piece(c, u);
    } else {
      open_op(c, "concat");
      for (i=0; i<k; i++) {
        pp_bit_piece(c, u);
      }
      close_op(c);
    }
    break;

  case BVSLICE_EXTRACT:
    u = d->desc.e.vector;
    i = d->desc.e.low;
    k = d->desc.e.high;
    assert(i <= k);
    if (i == 0 && k == term_bitsize(c->tbl, u) - 1) {
      pp_rec(c, u);
    } else {
      open_indexed_op(c, "extract", k, i, true);
      pp_rec(c, u);
      close_op(c);
    }
    break;

  case BVSLICE_CONST64:
    if (!c->dry) pp_smt2_bv64(&c->printer->pp, d->desc.c64.value, d->desc.c64.nbits);
    break;

  case BVSLICE_CONST:
    if (!c->dry) pp_clone_smt2_bv(&c->printer->pp, d->desc.c.value, d->desc.c.nbits);
    break;
  }
}

static void pp_bv_slices(smt2_term_pp_t *c, bvslice_t *d, uint32_t n) {
  uint32_t i;

  if (n == 1) {
    pp_bv_slice(c, d);
  } else {
    open_op(c, "concat");
    i = n;
    while (i > 0) {
      i --;
      pp_bv_slice(c, d + i);
    }
    close_op(c);
  }
}

static void pp_bit_array(smt2_term_pp_t *c, const term_t *a, uint32_t n) {
  bvslicer_t slicer;
  uint32_t i;

  init_bvslicer(&slicer);
  if (slice_bitarray(&slicer, c->tbl, a, n)) {
    pp_bv_slices(c, slicer.data, slicer.nelems);
  } else if (n == 1) {
    pp_bit_piece(c, a[0]);
  } else {
    open_op(c, "concat");
    i = n;
    while (i > 0) {
      i --;
      pp_bit_piece(c, a[i]);
    }
    close_op(c);
  }
  delete_bvslicer(&slicer);
}


/*
 * Atoms with a dual: (op a b) or (dual a b) if polarity is false
 */
static void pp_binary_atom(smt2_term_pp_t *c, const char *pos_op, const char *neg_op, composite_term_t *d, bool polarity) {
  assert(d->arity == 2);
  pp_nary(c, polarity ? pos_op : neg_op, d->arg, 2);
}

// equality: for Booleans, the negation is (not (= a b))
static void pp_equality(smt2_term_pp_t *c, composite_term_t *d, bool polarity) {
  bool as_real;

  assert(d->arity == 2);
  if (is_boolean_term(c->tbl, d->arg[0])) {
    open_neg(c, polarity);
    pp_nary(c, "=", d->arg, 2);
    close_neg(c, polarity);
  } else {
    as_real = is_real_valued(c, d->arg[0]) || is_real_valued(c, d->arg[1]);
    open_op(c, polarity ? "=" : "distinct");
    pp_arith_arg(c, d->arg[0], as_real);
    pp_arith_arg(c, d->arg[1], as_real);
    close_op(c);
  }
}

// (divides x y): x divides y
static void pp_divides(smt2_term_pp_t *c, composite_term_t *d, bool polarity) {
  term_t x, y;
  int32_t n;

  assert(d->arity == 2);
  x = d->arg[0];
  y = d->arg[1];

  open_neg(c, polarity);
  if (is_pos_term(x) && term_kind(c->tbl, x) == ARITH_CONSTANT &&
      q_get32(rational_term_desc(c->tbl, x), &n) && n > 0) {
    // ((_ divisible n) y)
    open_indexed_op(c, "divisible", (uint32_t) n, 0, false);
    pp_rec(c, y);
    close_op(c);
  } else {
    // (= (mod y x) 0)
    open_op(c, "=");
    open_op(c, "mod");
    pp_rec(c, y);
    pp_rec(c, x);
    close_op(c);
    put_zero(c, false);
    close_op(c);
  }
  close_neg(c, polarity);
}


/*
 * Term of index i (or its negation if polarity is false)
 */
static void pp_term_idx(smt2_term_pp_t *c, int32_t i, bool polarity) {
  term_table_t *tbl;
  composite_term_t *d;
  select_term_t *s;
  term_t t, x;
  uint32_t k;
  bool as_real;

  tbl = c->tbl;
  t = pos_term(i);
  assert(is_boolean_type(type_for_idx(tbl, i)) || polarity);

  switch (unchecked_kind_for_idx(tbl, i)) {
  case UNINTERPRETED_TERM:
  case VARIABLE:
    open_neg(c, polarity);
    put_name(c, i);
    close_neg(c, polarity);
    break;

  case ARITH_CONSTANT:
    put_rational(c, rational_for_idx(tbl, i), real_syntax(c, t));
    break;

  case BV64_CONSTANT:
    if (!c->dry) {
      pp_smt2_bv64(&c->printer->pp, bvconst64_for_idx(tbl, i)->value, bvconst64_for_idx(tbl, i)->bitsize);
    }
    break;

  case BV_CONSTANT:
    if (!c->dry) {
      pp_smt2_bv(&c->printer->pp, bvconst_for_idx(tbl, i)->data, bvconst_for_idx(tbl, i)->bitsize);
    }
    break;

  case ARITH_EQ_ATOM:
    x = integer_value_for_idx(tbl, i);
    pp_vs_zero(c, polarity ? "=" : "distinct", x);
    break;

  case ARITH_GE_ATOM:
    x = integer_value_for_idx(tbl, i);
    pp_vs_zero(c, polarity ? ">=" : "<", x);
    break;

  case ARITH_IS_INT_ATOM:
    open_neg(c, polarity);
    open_op(c, "is_int");
    pp_rec(c, integer_value_for_idx(tbl, i));
    close_op(c);
    close_neg(c, polarity);
    break;

  case ARITH_FLOOR:
    x = integer_value_for_idx(tbl, i);
    if (is_integer_term(tbl, x)) {
      pp_rec(c, x);
    } else {
      open_op(c, "to_int");
      pp_rec(c, x);
      close_op(c);
    }
    break;

  case ARITH_CEIL:
    // ceil(x) = - floor(- x)
    x = integer_value_for_idx(tbl, i);
    if (is_integer_term(tbl, x)) {
      pp_rec(c, x);
    } else {
      open_op(c, "-");
      open_op(c, "to_int");
      open_op(c, "-");
      pp_rec(c, x);
      close_op(c);
      close_op(c);
      close_op(c);
    }
    break;

  case ARITH_ABS:
    // (ite (>= x 0) x (- x))
    x = integer_value_for_idx(tbl, i);
    as_real = real_syntax(c, x);
    open_op(c, "ite");
    open_op(c, ">=");
    pp_rec(c, x);
    put_zero(c, as_real);
    close_op(c);
    pp_rec(c, x);
    open_op(c, "-");
    pp_rec(c, x);
    close_op(c);
    close_op(c);
    break;

  case OR_TERM:
    d = composite_for_idx(tbl, i);
    open_neg(c, polarity);
    pp_nary(c, "or", d->arg, d->arity);
    close_neg(c, polarity);
    break;

  case EQ_TERM:
  case ARITH_BINEQ_ATOM:
  case BV_EQ_ATOM:
    pp_equality(c, composite_for_idx(tbl, i), polarity);
    break;

  case BV_GE_ATOM:
    pp_binary_atom(c, "bvuge", "bvult", composite_for_idx(tbl, i), polarity);
    break;

  case BV_SGE_ATOM:
    pp_binary_atom(c, "bvsge", "bvslt", composite_for_idx(tbl, i), polarity);
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    d = composite_for_idx(tbl, i);
    as_real = is_real_valued(c, t);
    open_neg(c, polarity);
    open_op(c, "ite");
    pp_rec(c, d->arg[0]);
    pp_arith_arg(c, d->arg[1], as_real);
    pp_arith_arg(c, d->arg[2], as_real);
    close_op(c);
    close_neg(c, polarity);
    break;

  case APP_TERM:
    // (f a_1 ... a_n)
    d = composite_for_idx(tbl, i);
    open_neg(c, polarity);
    open_par(c);
    for (k=0; k<d->arity; k++) {
      pp_rec(c, d->arg[k]);
    }
    close_op(c);
    close_neg(c, polarity);
    break;

  case DISTINCT_TERM:
    d = composite_for_idx(tbl, i);
    open_neg(c, polarity);
    pp_nary(c, "distinct", d->arg, d->arity);
    close_neg(c, polarity);
    break;

  case XOR_TERM:
    d = composite_for_idx(tbl, i);
    open_neg(c, polarity);
    pp_nary(c, "xor", d->arg, d->arity);
    close_neg(c, polarity);
    break;

  case ARITH_RDIV:
    d = composite_for_idx(tbl, i);
    open_op(c, "/");
    pp_arith_arg(c, d->arg[0], true);
    pp_arith_arg(c, d->arg[1], true);
    close_op(c);
    break;

  case ARITH_IDIV:
    pp_nary(c, "div", composite_for_idx(tbl, i)->arg, 2);
    break;

  case ARITH_MOD:
    pp_nary(c, "mod", composite_for_idx(tbl, i)->arg, 2);
    break;

  case ARITH_DIVIDES_ATOM:
    pp_divides(c, composite_for_idx(tbl, i), polarity);
    break;

  case BV_DIV:
    pp_nary(c, "bvudiv", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_REM:
    pp_nary(c, "bvurem", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_SDIV:
    pp_nary(c, "bvsdiv", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_SREM:
    pp_nary(c, "bvsrem", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_SMOD:
    pp_nary(c, "bvsmod", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_SHL:
    pp_nary(c, "bvshl", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_LSHR:
    pp_nary(c, "bvlshr", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_ASHR:
    pp_nary(c, "bvashr", composite_for_idx(tbl, i)->arg, 2);
    break;

  case BV_ARRAY:
    d = composite_for_idx(tbl, i);
    pp_bit_array(c, d->arg, d->arity);
    break;

  case BIT_TERM:
    // (= ((_ extract i i) x) #b1)
    s = select_for_idx(tbl, i);
    open_neg(c, polarity);
    open_op(c, "=");
    open_indexed_op(c, "extract", s->idx, s->idx, true);
    pp_rec(c, s->arg);
    close_op(c);
    put_bit_const(c, true);
    close_op(c);
    close_neg(c, polarity);
    break;

  case POWER_PRODUCT:
    pp_pprod(c, pprod_for_idx(tbl, i));
    break;

  case ARITH_POLY:
    pp_poly(c, polynomial_for_idx(tbl, i), real_syntax(c, t));
    break;

  case BV64_POLY:
    pp_bvpoly64(c, bvpoly64_for_idx(tbl, i));
    break;

  case BV_POLY:
    pp_bvpoly(c, bvpoly_for_idx(tbl, i));
    break;

  case CONSTANT_TERM:       // scalar constants: no SMT-LIB 2 literal
  case ARITH_FF_CONSTANT:
  case ARITH_FF_EQ_ATOM:
  case ARITH_FF_BINEQ_ATOM:
  case ARITH_FF_POLY:
  case ARITH_ROOT_ATOM:
  case UPDATE_TERM:
  case TUPLE_TERM:
  case FORALL_TERM:
  case LAMBDA_TERM:
  case SELECT_TERM:
  case UNUSED_TERM:
  case RESERVED_TERM:
  default:
    fail(c);
    break;
  }
}

static void pp_rec(smt2_term_pp_t *c, term_t t) {
  assert(good_term(c->tbl, t));

  if (c->failed) return;

  if (t == true_term) {
    put_string(c, "true");
  } else if (t == false_term) {
    put_string(c, "false");
  } else {
    pp_term_idx(c, index_of(t), is_pos_term(t));
  }
}


/*
 * Print t in SMT-LIB 2 syntax
 */
bool smt2_pp_term(smt2_pp_t *printer, term_table_t *tbl, term_t t) {
  smt2_term_pp_t c;

  c.printer = printer;
  c.tbl = tbl;
  c.failed = false;

  // dry run
  c.dry = true;
  pp_rec(&c, t);
  if (c.failed) return false;

  c.dry = false;
  pp_rec(&c, t);

  return !c.failed;
}
