/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Print terms
 */

#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "io/term_printer.h"
#include "io/type_printer.h"
#include "terms/bv64_constants.h"


/*
 * Ids for primitive terms
 */
static const char * const term2string[] = {
  "const_idx", "(not const_idx)", "true", "false",
};


/*
 * Term id:
 */
void print_term_id(FILE *f, term_t t) {
  assert(t >= 0);

  if (t <= false_term) {
    fputs(term2string[t], f);
  } else if (is_neg_term(t)) {
    fprintf(f, "(not t!%"PRId32")", index_of(t));
  } else {
    fprintf(f, "t!%"PRId32, index_of(t));
  }
}


/*
 * Display power products
 */
static void print_varexp_array(FILE *f, varexp_t *a, uint32_t n) {
  uint32_t i, d;

  if (n == 0) {
    fprintf(f, "1");
    return;
  }
  d = a[0].exp;
  print_term_id(f, a[0].var);
  if (d != 1) {
    fprintf(f, "^%"PRIu32, d);
  }
  for (i=1; i<n; i++) {
    d = a[i].exp;
    fputc('*', f);
    print_term_id(f, a[i].var);
    if (d != 1) {
      fprintf(f, "^%"PRIu32, d);
    }
  }
}


/*
 * Polynomials, power products, and buffers
 */
void print_pprod(FILE *f, pprod_t *r) {
  if (pp_is_var(r)) {
    print_term_id(f, var_of_pp(r));
  } else if (pp_is_empty(r)) {
    fputc('1', f);
  } else if (r == end_pp) {
    fputs("end_pp", f);
  } else {
    print_varexp_array(f, r->prod, r->len);
  }
}


/*
 * Bit-vector polynomial
 */
static void print_bvmono(FILE *f, uint32_t *coeff, int32_t x, uint32_t n, bool first) {
  uint32_t w;

  w = (n + 31) >> 5; // number of words in coeff
  if (x == const_idx) {
    if (! first) fputs(" + ", f);
    bvconst_print(f, coeff, n);

  } else if (bvconst_is_one(coeff, w)) {
    if (! first) fputs(" + ", f);
    print_term_id(f, x);

  } else if (bvconst_is_minus_one(coeff, n)) {
    if (! first) fputc(' ', f);
    fputs("- ", f);
    print_term_id(f, x);

  } else {
    if (! first) fputs(" + ", f);
    bvconst_print(f, coeff, n);
    fputc('*', f);
    print_term_id(f, x);
  }
}

void print_bvpoly(FILE *f, bvpoly_t *p) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_bvmono(f, p->mono[i].coeff, p->mono[i].var, p->bitsize, first);
      first = false;
    }
  }
}


/*
 * Print buffer b
 */
static void print_bvarith_mono(FILE *f, uint32_t *coeff, pprod_t *r, uint32_t n, bool first) {
  uint32_t w;

  w = (n + 31) >> 5;
  if (pp_is_empty(r)) {
    if (! first) fprintf(f, " + ");
    bvconst_print(f, coeff, n);

  } else if (bvconst_is_one(coeff, w)) {
    if (! first) fprintf(f, " + ");
    print_pprod(f, r);

  } else if (bvconst_is_minus_one(coeff, n)) {
    if (! first) fprintf(f, " ");
    fprintf(f, "- ");
    print_pprod(f, r);

  } else {
    if (! first) fprintf(f, " + ");
    bvconst_print(f, coeff, n);
    fprintf(f, " ");
    print_pprod(f, r);
  }
}

void print_bvarith_buffer(FILE *f, bvarith_buffer_t *b) {
  bvmlist_t *p;
  bool first;

  if (bvarith_buffer_is_zero(b)) {
    fprintf(f, "0");
  } else {
    p = b->list;
    first = true;
    while (p->next != NULL) {
      print_bvarith_mono(f, p->coeff, p->prod, b->bitsize, first);
      first = false;
      p = p->next;
    }
  }
}

/*
 * Bit-vector polynomial, small coefficients
 */
static void print_bvconst64(FILE *f, uint64_t c, uint32_t n) {
  char x;

  fprintf(f, "0b");
  while (n > 0) {
    n --;
    x = '0';
    if (tst_bit64(c, n)) {
      x = '1';
    }
    fprintf(f, "%c", x);
  }
}

static void print_bvmono64(FILE *f, uint64_t coeff, int32_t x, uint32_t n, bool first) {
  if (x == const_idx) {
    if (! first) fputs(" + ", f);
    print_bvconst64(f, coeff, n);

  } else if (coeff == 1) {
    if (! first) fputs(" + ", f);
    print_term_id(f, x);

  } else if (bvconst64_is_minus_one(coeff, n)) {
    if (! first) fputc(' ', f);
    fputs("- ", f);
    print_term_id(f, x);

  } else {
    if (! first) fputs(" + ", f);
    print_bvconst64(f, coeff, n);
    fputc('*', f);
    print_term_id(f, x);
  }
}

void print_bvpoly64(FILE *f, bvpoly64_t *p) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_bvmono64(f, p->mono[i].coeff, p->mono[i].var, p->bitsize, first);
      first = false;
    }
  }
}


/*
 * Print buffer b
 */
static void print_bvarith64_mono(FILE *f, uint64_t coeff, pprod_t *r, uint32_t n, bool first) {
  if (pp_is_empty(r)) {
    if (! first) fprintf(f, " + ");
    print_bvconst64(f, coeff, n);

  } else if (coeff == 1) {
    if (! first) fprintf(f, " + ");
    print_pprod(f, r);

  } else if (bvconst64_is_minus_one(coeff, n)) {
    if (! first) fprintf(f, " ");
    fprintf(f, "- ");
    print_pprod(f, r);

  } else {
    if (! first) fprintf(f, " + ");
    print_bvconst64(f, coeff, n);
    fprintf(f, " ");
    print_pprod(f, r);
  }
}

void print_bvarith64_buffer(FILE *f, bvarith64_buffer_t *b) {
  bvmlist64_t *p;
  bool first;

  if (bvarith64_buffer_is_zero(b)) {
    fprintf(f, "0");
  } else {
    p = b->list;
    first = true;
    while (p->next != NULL) {
      print_bvarith64_mono(f, p->coeff, p->prod, b->bitsize, first);
      first = false;
      p = p->next;
    }
  }
}



/*
 * Bit-array buffer
 */
static void print_bit(FILE *f, bit_t b) {
  if (b == true_bit) {
    fprintf(f, "tt");
  } else if (b == false_bit) {
    fprintf(f, "ff");
  } else {
    if (bit_is_neg(b)) fprintf(f, "~");
    fprintf(f, "b!%"PRId32, node_of_bit(b));
  }
}

void print_bvlogic_buffer(FILE *f, bvlogic_buffer_t *b) {
  uint32_t i, n;

  n = b->bitsize;
  fprintf(f, "[");
  if (n > 0) {
    print_bit(f, b->bit[0]);
    for (i=1; i<n; i++) {
      fprintf(f, " ");
      print_bit(f, b->bit[i]);
    }
  }
  fprintf(f, "]");
}


/*
 * Term name
 */
void print_term_name(FILE *f, term_table_t *tbl, term_t t) {
  char *name;

  assert(good_term(tbl, t));

  name = term_name(tbl, t);
  if (t <= false_term || name == NULL) {
    print_term_id(f, t);
  } else {
    fputs(name, f);
  }
}




/*
 * Code/prefix for a term kind
 */

/*
 * Table to convert term_kind to string
 */
static const char * const tag2string[NUM_TERM_KINDS] = {
  "unused",
  "reserved",
  "constant",
  "bv64-const",
  "bv-const",
  "uninterpreted",
  "ite",
  "eq",
  "distinct",
  "or",
  "xor",
  "bool-to-bv",  // aka bv-array
  "bvdiv",
  "bvrem",
  "bvsdiv",
  "bvsrem",
  "bvsmod",
  "bvshl",
  "bvlshr",
  "bvashr",
  "bveq",
  "bvge",
  "bvsge",
  "bit",
  "pprod",
  "bv64-poly",
  "bv-poly",
};



/*
 * Recursively print term t: if level <= 0, don't expand term that have a name
 */
static void print_term_recur(FILE *f, term_table_t *tbl, term_t t, int32_t level);

// generic composite
static void print_composite_term(FILE *f, term_table_t *tbl, term_kind_t tag, composite_term_t *d, int32_t level) {
  uint32_t i, n;

  assert(ITE_TERM <= tag && tag <= BV_SGE_ATOM);
  fputc('(', f);
  fputs(tag2string[tag], f);
  n = d->arity;
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_term_recur(f, tbl, d->arg[i], level);
  }
  fputc(')', f);
}

// select: printed as (bit <bv> <idx>)
static void print_select_term(FILE *f, term_table_t *tbl, term_kind_t tag, select_term_t *d, int32_t level) {
  uint32_t idx;

  assert(tag == BIT_TERM);

  idx = d->idx;
  fprintf(f, "(%s ", tag2string[tag]);
  print_term_recur(f, tbl, d->arg, level);
  fprintf(f, " %"PRIu32")", idx);
}

// bitvector polynomial
static void print_bvmono_recur(FILE *f, term_table_t *tbl, uint32_t *coeff, int32_t x, uint32_t n, bool first, int32_t level) {
  uint32_t w;

  w = (n + 31) >> 5;
  if (x == const_idx) {
    if (! first) fputs(" + ", f);
    bvconst_print(f, coeff, n);

  } else if (bvconst_is_one(coeff, w)) {
    if (! first) fputs(" + ", f);
    print_term_recur(f, tbl, x, level);

  } else if (bvconst_is_minus_one(coeff, n)) {
    if (! first) fputc(' ', f);
    fputs("- ", f);
    print_term_recur(f, tbl, x, level);

  } else {
    if (! first) fputs(" + ", f);
    bvconst_print(f, coeff, n);
    fputc('*', f);
    print_term_recur(f, tbl, x, level);
  }
}

static void print_bvpoly_term(FILE *f, term_table_t *tbl, bvpoly_t *p, int32_t level) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_bvmono_recur(f, tbl, p->mono[i].coeff, p->mono[i].var, p->bitsize, first, level);
      first = false;
    }
  }
}

// 64bit bit-vector polynomial
static void print_bvmono64_recur(FILE *f, term_table_t *tbl, uint64_t coeff, int32_t x, uint32_t n, bool first, int32_t level) {
  if (x == const_idx) {
    if (! first) fputs(" + ", f);
    print_bvconst64(f, coeff, n);

  } else if (coeff == 1) {
    if (! first) fputs(" + ", f);
    print_term_recur(f, tbl, x, level);

  } else if (bvconst64_is_minus_one(coeff, n)) {
    if (! first) fputc(' ', f);
    fputs("- ", f);
    print_term_recur(f, tbl, x, level);

  } else {
    if (! first) fputs(" + ", f);
    print_bvconst64(f, coeff, n);
    fputc('*', f);
    print_term_recur(f, tbl, x, level);
  }
}

static void print_bvpoly64_term(FILE *f, term_table_t *tbl, bvpoly64_t *p, int32_t level) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_bvmono64_recur(f, tbl, p->mono[i].coeff, p->mono[i].var, p->bitsize, first, level);
      first = false;
    }
  }
}


// power product
static void print_power_product_term(FILE *f, term_table_t *tbl, pprod_t *r, int32_t level) {
  uint32_t i, n;

  assert(r != empty_pp && r != end_pp && !pp_is_var(r));

  n = r->len;

  assert(n > 0);
  print_term_recur(f, tbl, r->prod[0].var, level);
  if (r->prod[0].exp > 1) {
    fprintf(f, "^%"PRIu32, r->prod[0].exp);
  }
  for (i=1; i<n; i++) {
    fputc('*', f);
    print_term_recur(f, tbl, r->prod[i].var, level);
    if (r->prod[i].exp > 1) {
    fprintf(f, "^%"PRIu32, r->prod[i].exp);
    }
  }
}

// bvconstant
static void print_bvconst_term(FILE *f, bvconst_term_t *d) {
  bvconst_print(f, d->data, d->bitsize);
}

static void print_bvconst64_term(FILE *f, bvconst64_term_t *d) {
  print_bvconst64(f, d->value, d->bitsize);
}

static void print_term_idx_recur(FILE *f, term_table_t *tbl, int32_t i, int32_t level) {
  char *name;

  name = term_name(tbl, pos_term(i));
  switch (tbl->kind[i]) {
  case CONSTANT_TERM:
    if (name != NULL) {
      fputs(name, f);
    } else {
      fprintf(f, "(const %"PRId32" of type ", tbl->desc[i].integer);
      print_type_name(f, tbl->types, tbl->type[i]);
      fputc(')', f);
    }
    break;

  case UNINTERPRETED_TERM:
    if (name != NULL) {
      fputs(name, f);
    } else {
      fprintf(f, "(unint of type ");
      print_type_name(f, tbl->types, tbl->type[i]);
      fputc(')', f);
    }
    break;

  case BV64_CONSTANT:
    print_bvconst64_term(f, tbl->desc[i].ptr);
    break;

  case BV_CONSTANT:
    print_bvconst_term(f, tbl->desc[i].ptr);
    break;

  case ITE_TERM:
  case EQ_TERM:
  case DISTINCT_TERM:
  case OR_TERM:
  case XOR_TERM:
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
    // i's descriptor is a composite term
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      print_composite_term(f, tbl, tbl->kind[i], tbl->desc[i].ptr, level - 1);
    }
    break;

  case BIT_TERM:
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      print_select_term(f, tbl, tbl->kind[i], &tbl->desc[i].select, level - 1);
    }
    break;

  case POWER_PRODUCT:
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      print_power_product_term(f, tbl, tbl->desc[i].ptr, level - 1);
    }
    break;

  case BV64_POLY:
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      print_bvpoly64_term(f, tbl, tbl->desc[i].ptr, level - 1);
    }
    break;

  case BV_POLY:
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      print_bvpoly_term(f, tbl, tbl->desc[i].ptr, level - 1);
    }
    break;

  case UNUSED_TERM:
  case RESERVED_TERM:
  default:
    fprintf(f, "bad-term-%"PRIu32, i);
    break;
  }
}

static void print_term_recur(FILE *f, term_table_t *tbl, term_t t, int32_t level) {
  int32_t i;

  if (t <= false_term) {
    fputs(term2string[t], f);
  } else {
    i = index_of(t);
    if (is_neg_term(t)) {
      fputs("(not ", f);
      print_term_idx_recur(f, tbl, i, level - 1);
      fputc(')', f);
    } else {
      print_term_idx_recur(f, tbl, i, level);
    }
  }
}


/*
 * Print term expression t: expand names at the outer level only
 */
void print_term_exp(FILE *f, term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t));
  print_term_recur(f, tbl, t, 1);
}


/*
 * Print full term expression t: expand all names
 */
void print_term_full(FILE *f, term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t));
  print_term_recur(f, tbl, t, INT32_MAX);
}


/*
 * Default print: print t's name if it has one, or the expression otherwise
 */
void print_term(FILE *f, term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t));
  print_term_recur(f, tbl, t, 0);
}


/*
 * Term definition: name := expr
 */
void print_term_def(FILE *f, term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t));
  print_term_name(f, tbl, t);
  fputs(" := ", f);
  print_term_recur(f, tbl, t, 1);
}



/*
 * WHOLE TERM TABLE
 */

#if 0

// NOT USED
/*
 * Print t's name unless it's a constant or a negation
 */
static void print_name_or_constant(FILE *f, term_table_t *tbl, term_t t) {
  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    assert(is_pos_term(t));
    print_bvconst64_term(f, bvconst64_term_desc(tbl, t));
    break;

  case BV_CONSTANT:
    assert(is_pos_term(t));
    print_bvconst_term(f, bvconst_term_desc(tbl, t));
    break;

  default:
    if (t <= false_term) {
      fputs(term2string[t], f);
    } else if (is_neg_term(t)) {
      fputs("(not ", f);
      print_term_name(f, tbl, opposite_term(t));
      fputc(')', f);
    } else {
      print_term_name(f, tbl, t);
    }
    break;
  }
}

#endif

/*
 * Variant: t's id unless it's a constant
 */
static void print_id_or_constant(FILE *f, term_table_t *tbl, term_t t) {
  switch (term_kind(tbl, t)) {
  case BV64_CONSTANT:
    assert(is_pos_term(t));
    print_bvconst64_term(f, bvconst64_term_desc(tbl, t));
    break;

  case BV_CONSTANT:
    assert(is_pos_term(t));
    print_bvconst_term(f, bvconst_term_desc(tbl, t));
    break;

  default:
    if (t <= false_term) {
      fputs(term2string[t], f);
    } else if (is_neg_term(t)) {
      fputs("(not ", f);
      print_term_id(f, opposite_term(t));
      fputc(')', f);
    } else {
      print_term_id(f, t);
    }
    break;
  }
}


/*
 * Maximal length of all names in tbl
 * - return 0 if no type has a name
 */
static uint32_t max_term_name_length(term_table_t *tbl) {
  char *name;
  uint32_t max, l, n, i;

  max = 0;
  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (tbl->kind[i] != UNUSED_TERM) {
      name = term_name(tbl, pos_term(i));
      if (name != NULL) {
        l = strlen(name);
        if (l > max) {
          max = l;
        }
      }
    }
  }

  return max;
}


/*
 * Print n blanks
 */
static void print_spaces(FILE *f, uint32_t n) {
  while (n > 0) {
    fputc(' ', f);
    n --;
  }
}


/*
 * Print string s, and add enough spaces to get to length l.
 * - if s is too long, print s and add one space
 */
static void print_padded_string(FILE *f, char *s, uint32_t l) {
  if (s == NULL) {
    print_spaces(f, l);
  } else if (l >= strlen(s)) {
    while (*s != '\0') {
      fputc(*s, f);
      s ++;
      l --;
    }
    print_spaces(f, l);
  } else {
    fprintf(f, "%s ", s);
  }
}


// generic composite
static void print_composite(FILE *f, term_table_t *tbl, term_kind_t tag, composite_term_t *d) {
  uint32_t i, n;

  assert(ITE_TERM <= tag && tag <= BV_SGE_ATOM);
  fputc('(', f);
  fputs(tag2string[tag], f);
  n = d->arity;
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_id_or_constant(f, tbl, d->arg[i]);
  }
  fputc(')', f);
}

// select
static void print_select(FILE *f, term_table_t *tbl, term_kind_t tag, select_term_t *d) {
  uint32_t idx;

  assert(tag == BIT_TERM);
  idx = d->idx;
  fprintf(f, "(%s ", tag2string[tag]);
  print_id_or_constant(f, tbl, d->arg);
  fprintf(f, " %"PRIu32")", idx);
}


// power product
static void print_named_varexp_array(FILE *f, term_table_t *tbl, varexp_t *a, uint32_t n) {
  uint32_t i, d;

  if (n == 0) {
    fprintf(f, "1");
    return;
  }
  d = a[0].exp;
  print_id_or_constant(f, tbl, a[0].var);
  if (d != 1) {
    fprintf(f, "^%"PRIu32, d);
  }
  for (i=1; i<n; i++) {
    d = a[i].exp;
    fputc('*', f);
    print_id_or_constant(f, tbl, a[i].var);
    if (d != 1) {
      fprintf(f, "^%"PRIu32, d);
    }
  }
}

static void print_named_pprod(FILE *f, term_table_t *tbl, pprod_t *r) {
  if (pp_is_var(r)) {
    print_id_or_constant(f, tbl, var_of_pp(r));
  } else if (pp_is_empty(r)) {
    fputc('1', f);
  } else if (r == end_pp) {
    fputs("end_pp", f);
  } else {
    print_named_varexp_array(f, tbl, r->prod, r->len);
  }
}

// bitvector polynomials
static void print_named_bvmono(FILE *f, term_table_t *tbl, uint32_t *coeff,
                               int32_t x, uint32_t n, bool first) {
  uint32_t w;

  w = (n + 31) >> 5;
  if (x == const_idx) {
    if (! first) fputs(" + ", f);
    bvconst_print(f, coeff, n);

  } else if (bvconst_is_one(coeff, w)) {
    if (! first) fputs(" + ", f);
    print_id_or_constant(f, tbl, x);

  } else if (bvconst_is_minus_one(coeff, n)) {
    if (! first) fputc(' ', f);
    fputs("- ", f);
    print_id_or_constant(f, tbl, x);

  } else {
    if (! first) fputs(" + ", f);
    bvconst_print(f, coeff, n);
    fputc('*', f);
    print_id_or_constant(f, tbl, x);

  }
}

static void print_named_bvpoly(FILE *f, term_table_t *tbl, bvpoly_t *p) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_named_bvmono(f, tbl, p->mono[i].coeff, p->mono[i].var, p->bitsize, first);
      first = false;
    }
  }
}

// bitvector polynomials with small coefficients
static void print_named_bvmono64(FILE *f, term_table_t *tbl, uint64_t coeff,
                                 int32_t x, uint32_t n, bool first) {
  if (x == const_idx) {
    if (! first) fputs(" + ", f);
    print_bvconst64(f, coeff, n);

  } else if (coeff == 1) {
    if (! first) fputs(" + ", f);
    print_id_or_constant(f, tbl, x);

  } else if (bvconst64_is_minus_one(coeff, n)) {
    if (! first) fputc(' ', f);
    fputs("- ", f);
    print_id_or_constant(f, tbl, x);

  } else {
    if (! first) fputs(" + ", f);
    print_bvconst64(f, coeff, n);
    fputc('*', f);
    print_id_or_constant(f, tbl, x);
  }
}

static void print_named_bvpoly64(FILE *f, term_table_t *tbl, bvpoly64_t *p) {
  uint32_t i, n;
  bool first;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    first = true;
    for (i=0; i<n; i++) {
      print_named_bvmono64(f, tbl, p->mono[i].coeff, p->mono[i].var, p->bitsize, first);
      first = false;
    }
  }
}




/*
 * Print all terms in tbl
 */
void print_term_table(FILE *f, term_table_t *tbl) {
  uint32_t i, n;
  uint32_t name_size;

  name_size = max_term_name_length(tbl) + 2;
  if (name_size < 4) {
    name_size = 4;
  } else if (name_size > 20) {
    name_size = 20;
  }

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (tbl->kind[i] != UNUSED_TERM) {
      // id + name
      fprintf(f, "%4"PRIu32" ", i);
      print_padded_string(f, term_name(tbl, pos_term(i)), name_size);

      // definition
      switch (tbl->kind[i]) {
      case RESERVED_TERM:
        fprintf(f, "reserved");
        break;

      case CONSTANT_TERM:
        if (i == bool_const) {
          fprintf(f, "true");
        } else {
          fprintf(f, "(const %"PRId32" of type ", tbl->desc[i].integer);
          print_type_name(f, tbl->types, tbl->type[i]);
          fputc(')', f);
        }
        break;

      case UNINTERPRETED_TERM:
        fprintf(f, "(unint of type ");
        print_type_name(f, tbl->types, tbl->type[i]);
        fputc(')', f);
        break;

      case BV64_CONSTANT:
        print_bvconst64_term(f, tbl->desc[i].ptr);
        break;

      case BV_CONSTANT:
        print_bvconst_term(f, tbl->desc[i].ptr);
        break;

      case ITE_TERM:
      case EQ_TERM:
      case DISTINCT_TERM:
      case OR_TERM:
      case XOR_TERM:
      case BV_ARRAY:
      case BV_DIV:
      case BV_REM:
      case BV_SDIV:
      case BV_SREM:
      case BV_SMOD:
      case BV_SHL:
      case BV_LSHR:
      case BV_ASHR:
      case BV_EQ_ATOM:
      case BV_GE_ATOM:
      case BV_SGE_ATOM:
        // i's descriptor is a composite term
        print_composite(f, tbl, tbl->kind[i], tbl->desc[i].ptr);
        break;

      case BIT_TERM:
        print_select(f, tbl, tbl->kind[i], &tbl->desc[i].select);
        break;

      case POWER_PRODUCT:
        print_named_pprod(f, tbl, tbl->desc[i].ptr);
        break;

      case BV64_POLY:
        print_named_bvpoly64(f, tbl, tbl->desc[i].ptr);
        break;

      case BV_POLY:
        print_named_bvpoly(f, tbl, tbl->desc[i].ptr);
        break;

      default:
        fprintf(f, "bad-term-%"PRIu32, i);
        break;
      }

      fputc('\n', f);
    }
  }
}



/*************************
 *  NON-RECURSIVE PRINT  *
 ************************/

/*
 * Descriptor of term idx i
 */
static void print_term_idx_desc(FILE *f, term_table_t *tbl, int32_t i) {
  switch (tbl->kind[i]) {
  case UNUSED_TERM:
  case RESERVED_TERM:
    fprintf(f, "bad-term%"PRId32, i);
    break;

  case CONSTANT_TERM:
  case UNINTERPRETED_TERM:
    print_term_name(f, tbl, pos_term(i));
    break;

  case BV64_CONSTANT:
    print_bvconst64_term(f, tbl->desc[i].ptr);
    break;

  case BV_CONSTANT:
    print_bvconst_term(f, tbl->desc[i].ptr);
    break;

  case ITE_TERM:
  case EQ_TERM:
  case DISTINCT_TERM:
  case OR_TERM:
  case XOR_TERM:
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
    // i's descriptor is a composite term
    print_composite(f, tbl, tbl->kind[i], tbl->desc[i].ptr);
    break;

  case BIT_TERM:
    print_select(f, tbl, tbl->kind[i], &tbl->desc[i].select);
    break;

  case POWER_PRODUCT:
    print_named_pprod(f, tbl, tbl->desc[i].ptr);
    break;

  case BV64_POLY:
    print_named_bvpoly64(f, tbl, tbl->desc[i].ptr);
    break;

  case BV_POLY:
    print_named_bvpoly(f, tbl, tbl->desc[i].ptr);
    break;

  default:
    fprintf(f, "bad-term%"PRId32, i);
    break;
  }
}

/*
 * Print t's descriptor
 */
void print_term_desc(FILE *f, term_table_t *tbl, term_t t) {
  assert(t >= 0);

  if (t <= false_term) {
    fputs(term2string[t], f);
  } else {
    if (is_neg_term(t)) fputs("(not ", f);
    print_term_idx_desc(f, tbl, index_of(t));
    if (is_neg_term(t)) fputc(')', f);
  }
}


/*********************
 *  PRETTY PRINTING  *
 ********************/

/*
 * Term name
 */
void pp_term_name(yices_pp_t *printer, term_table_t *tbl, term_t t) {
  char *name;

  assert(good_term(tbl, t));

  if (t <= false_term) {
    name = (char *) term2string[t];
  } else {
    name = term_name(tbl, t);
  }

  if (name != NULL) {
    pp_string(printer, name);
  } else if (is_neg_term(t)) {
    pp_open_block(printer, PP_OPEN_NOT);
    pp_id(printer, "t!", index_of(t));
    pp_close_block(printer, true);
  } else {
    pp_id(printer, "t!", index_of(t));
  }
}



/*
 * Table: convert term_kind tag into the corresponding open_block tag
 * term_kind2block[k] = 0 means k is atomic or can't be printed
 * (Note this is ok, since 0 is PP_OPEN).
 */
static const pp_open_type_t term_kind2block[NUM_TERM_KINDS] = {
  0,                 //  UNUSED_TERM
  0,                 //  RESERVED_TERM

  0,                 //  CONSTANT_TERM
  0,                 //  BV64_CONSTANT
  0,                 //  BV_CONSTANT

  0,                 //  UNINTERPRETED_TERM

  PP_OPEN_ITE,       //  ITE_TERM
  PP_OPEN_EQ,        //  EQ_TERM
  PP_OPEN_DISTINCT,  //  DISTINCT_TERM
  PP_OPEN_OR,        //  OR_TERM
  PP_OPEN_XOR,       //  XOR_TERM
  PP_OPEN_BV_ARRAY,  //  BV_ARRAY
  PP_OPEN_BV_DIV,    //  BV_DIV
  PP_OPEN_BV_REM,    //  BV_REM
  PP_OPEN_BV_SDIV,   //  BV_SDIV
  PP_OPEN_BV_SREM,   //  BV_SREM
  PP_OPEN_BV_SMOD,   //  BV_SMOD
  PP_OPEN_BV_SHL,    //  BV_SHL
  PP_OPEN_BV_LSHR,   //  BV_LSHR
  PP_OPEN_BV_ASHR,   //  BV_ASHR
  PP_OPEN_EQ,        //  BV_EQ_ATOM
  PP_OPEN_BV_GE,     //  BV_GE_ATOM
  PP_OPEN_BV_SGE,    //  BV_SGE_ATOM

  PP_OPEN_BIT,       //  BIT_TERM

  PP_OPEN_PROD,      //  POWER_PRODUCT
  PP_OPEN_SUM,       //  BV64_POLY
  PP_OPEN_SUM,       //  BV_POLY
};


/*
 * Print term t (or not t)
 * - expand the term names if level > 0
 * - if polarity is true, print t, otherwise print its negation
 */
static void pp_term_recur(yices_pp_t *printer, term_table_t *tbl, term_t t, int32_t level, bool polariyt);


/*
 * Default print function for composites (including function applications)
 */
static void pp_composite_term(yices_pp_t *printer, term_table_t *tbl, term_kind_t tag, composite_term_t *d, int32_t level) {
  uint32_t i, n;
  pp_open_type_t op;

  assert(ITE_TERM <= tag && tag <= BV_SGE_ATOM);
  op = term_kind2block[tag];
  assert(op != 0);
  pp_open_block(printer, op);
  n = d->arity;
  for (i=0; i<n; i++) {
    pp_term_recur(printer, tbl, d->arg[i], level, true);
  }
  pp_close_block(printer, true);
}


/*
 * Binary atom: depending on the polarity, we use different 'op'
 * - example: (eq t1 t2) is printed as (= t1 t2) in positive context
 *                                  or (/= t1 t2) in a negative context
 */
static void pp_binary_atom(yices_pp_t *printer, term_table_t *tbl, pp_open_type_t op, composite_term_t *d, uint32_t level) {
  assert(d->arity == 2);

  pp_open_block(printer, op);
  pp_term_recur(printer, tbl, d->arg[0], level, true);
  pp_term_recur(printer, tbl, d->arg[1], level, true);
  pp_close_block(printer, true);
}


/*
 * Heuristic to estimate (crudely) whether it's nicer to print t in a
 * positive context or a negative context.
 * - high positive score means --> better to print t than (not t)
 * - high negative score means --> better to print (not t) than t
 */
static double p_score(term_table_t *tbl, term_t t) {
  composite_term_t *d;
  double score;
  uint32_t i, n;

  switch (term_kind(tbl, t)) {
  case OR_TERM:
    score = 0.0;
    d = or_term_desc(tbl, t);
    n = d->arity;
    for (i=0; i<n; i++) {
      if (is_pos_term(d->arg[i])) {
        score += 1.0;
      } else {
        score -= 1.0;
      }
    }
    break;

  default:
    score = 1.0;
    break;
  }

  if (is_neg_term(t)) {
    score = - score;
  }

  return score;
}


/*
 * or:
 * - if polarity is true and arity n > 2, we print (OR p1 ... p_n )
 * - if polarity is false, we print (AND (not p1) ... (not p_n))
 * - if polarity is true and arity n = 2
 *   we try to print as (IMPLY p1 p2) if one of the child has positive polarity and the other one has negative polarity
 */
static void pp_or_term(yices_pp_t *printer, term_table_t *tbl, composite_term_t *d, uint32_t level, bool polarity) {
  uint32_t i, n;
  pp_open_type_t op;
  term_t p, q;
  double sp, sq;

  n = d->arity;
  assert(n >= 2);

  if (polarity && n == 2) {
    // check if we can write this as an implication
    p = d->arg[0];
    q = d->arg[1];

    sp = p_score(tbl, p);
    sq = p_score(tbl, q);

    if (sp < 0.0 && sp < sq) {
      // (or p q) written as (implies (not p) q)
      pp_open_block(printer, PP_OPEN_IMPLIES);
      pp_term_recur(printer, tbl, p, level, false);
      pp_term_recur(printer, tbl, q, level, true);
      pp_close_block(printer, true);
      return;
    }

    if (sq < 0.0 && sq < sp) {
      // (or p q) written as (implies (not q) p)
      pp_open_block(printer, PP_OPEN_IMPLIES);
      pp_term_recur(printer, tbl, q, level, false);
      pp_term_recur(printer, tbl, p, level, true);
      pp_close_block(printer, true);
      return;
    }
  }

  op = polarity ? PP_OPEN_OR : PP_OPEN_AND;
  pp_open_block(printer, op);
  for (i=0; i<n; i++) {
    pp_term_recur(printer, tbl, d->arg[i], level, polarity);
  }
  pp_close_block(printer, true);
}


// select
static void pp_select_term(yices_pp_t *printer, term_table_t *tbl, term_kind_t tag, select_term_t *d, int32_t level) {
  pp_open_type_t op;
  uint32_t idx;

  assert(tag == BIT_TERM);
  op = term_kind2block[tag];
  assert(op != 0);
  idx = d->idx;
  pp_open_block(printer, op);
  pp_term_recur(printer, tbl, d->arg, level, true);
  pp_uint32(printer, idx);
  pp_close_block(printer, true);
}


// exponent (bv-pow x d)
static void pp_exponent(yices_pp_t *printer, term_table_t *tbl, term_t x, uint32_t d, int32_t level) {
  assert(d > 0);
  if (d == 1) {
    pp_term_recur(printer, tbl, x, level, true);
  } else {
    pp_open_block(printer, PP_OPEN_BV_POWER);
    pp_term_recur(printer, tbl, x, level, true);
    pp_uint32(printer, d);
    pp_close_block(printer, true);
  }
}

// power product (bv-mul ....)
static void pp_pprod(yices_pp_t *printer, term_table_t *tbl, pprod_t *p, int32_t level) {
  uint32_t i, n;

  n = p->len;
  assert(n > 0);
  if (n == 1) {
    pp_exponent(printer, tbl, p->prod[0].var, p->prod[0].exp, level);
  } else {
    pp_open_block(printer, PP_OPEN_BV_PROD);
    for (i=0; i<n; i++) {
      pp_exponent(printer, tbl, p->prod[i].var, p->prod[i].exp, level);
    }
    pp_close_block(printer, true);
  }
}

// bitvector monomial (* c x)
static void pp_bvmono64(yices_pp_t *printer, term_table_t *tbl, uint64_t c, uint32_t nbits, int32_t x, int32_t level) {
  pprod_t *p;
  uint32_t i, n;

  assert(x == const_idx || good_term(tbl, x));

  if (x == const_idx) {
    pp_bv64(printer, c, nbits);
  } else if (c == 1) {
    pp_term_recur(printer, tbl, x, level, true);
  } else {
    pp_open_block(printer, PP_OPEN_BV_PROD);
    pp_bv64(printer, c, nbits);
    if (term_kind(tbl, x) == POWER_PRODUCT) {
      p = pprod_term_desc(tbl, x);
      n = p->len;
      for (i=0; i<n; i++) {
        pp_exponent(printer, tbl, p->prod[i].var, p->prod[i].exp, level);
      }
    } else {
      pp_term_recur(printer, tbl, x, level, true);
    }
    pp_close_block(printer, true);
  }
}

// bitvector polynomial (+ mono1 ... mono_k), small coefficients
static void pp_bvpoly64(yices_pp_t *printer, term_table_t *tbl, bvpoly64_t *p, int32_t level) {
  uint32_t i, n;
  uint32_t nbits;

  n = p->nterms;
  nbits = p->bitsize;
  if (n == 1) {
    pp_bvmono64(printer, tbl, p->mono[0].coeff, nbits, p->mono[0].var, level);
  } else {
    pp_open_block(printer, PP_OPEN_BV_SUM);
    for (i=0; i<n; i++) {
      pp_bvmono64(printer, tbl, p->mono[i].coeff, nbits, p->mono[i].var, level);
    }
    pp_close_block(printer, true);
  }
}

// bitvector monomial (more than 64bits)
static void pp_bvmono(yices_pp_t *printer, term_table_t *tbl, uint32_t *c, uint32_t nbits, int32_t x, int32_t level) {
  pprod_t *p;
  uint32_t i, n, k;

  assert(x == const_idx || good_term(tbl, x));

  k = (nbits + 31) >> 5; // word size

  if (x == const_idx) {
    pp_bv(printer, c, nbits);
  } else if (bvconst_is_one(c, k)) {
    pp_term_recur(printer, tbl, x, level, true);
  } else {
    pp_open_block(printer, PP_OPEN_BV_PROD);
    pp_bv(printer, c, nbits);
    if (term_kind(tbl, x) == POWER_PRODUCT) {
      p = pprod_term_desc(tbl, x);
      n = p->len;
      for (i=0; i<n; i++) {
        pp_exponent(printer, tbl, p->prod[i].var, p->prod[i].exp, level);
      }
    } else {
      pp_term_recur(printer, tbl, x, level, true);
    }
    pp_close_block(printer, true);
  }
}

// bitvector polynomial (more than 64bits)
static void pp_bvpoly(yices_pp_t *printer, term_table_t *tbl, bvpoly_t *p, int32_t level) {
  uint32_t i, n;
  uint32_t nbits;

  n = p->nterms;
  nbits = p->bitsize;
  if (n == 1) {
    pp_bvmono(printer, tbl, p->mono[0].coeff, nbits, p->mono[0].var, level);
  } else {
    pp_open_block(printer, PP_OPEN_BV_SUM);
    for (i=0; i<n; i++) {
      pp_bvmono(printer, tbl, p->mono[i].coeff, nbits, p->mono[i].var, level);
    }
    pp_close_block(printer, true);
  }
}

// bitvector constants
static void pp_bvconst_term(yices_pp_t *printer, bvconst_term_t *d) {
  pp_bv(printer, d->data, d->bitsize);
}

static void pp_bvconst64_term(yices_pp_t *printer, bvconst64_term_t *d) {
  pp_bv64(printer, d->value, d->bitsize);
}


/*
 * Array of booleans:
 * - try to recognize zero/sign extend/extract/concat/shift
 * - if that fails, prints (bool-to-bv .... )
 */
static void pp_bit_array(yices_pp_t *printer, term_table_t *tbl, term_t *a, uint32_t n,  int32_t level) {
  uint32_t i;

  // TBD: decompose into slice here then print the concatenation of slices
  // if that fails, use the default below

  pp_open_block(printer, PP_OPEN_BV_ARRAY);
  for (i=0; i<n; i++) {
    pp_term_recur(printer, tbl, a[i], level, true);
  }
  pp_close_block(printer, true);
}

static void pp_bvarray_term(yices_pp_t *printer, term_table_t *tbl, composite_term_t *d, int32_t level) {
  pp_bit_array(printer, tbl, d->arg, d->arity, level);
}




/*
 * Name for i or (not i)
 */
static void pp_term_idx_name(yices_pp_t *printer, term_table_t *tbl, int32_t i, bool polarity) {
  char *name;

  name = term_name(tbl, pos_term(i));

  if (!polarity) {
    pp_open_block(printer, PP_OPEN_NOT);
  }
  if (name != NULL) {
    pp_string(printer, name);
  } else {
    pp_id(printer, "t!", i);
  }
  if (!polarity) {
    pp_close_block(printer, true);
  }
}

/*
 * term idx i or (not i)
 */
static void pp_term_idx(yices_pp_t *printer, term_table_t *tbl, int32_t i, int32_t level, bool polarity) {
  pp_open_type_t op;

  assert(is_boolean_type(tbl->type[i]) || polarity);

  if (level <= 0) {
    pp_term_idx_name(printer, tbl, i, polarity);
    return;
  }

  switch (tbl->kind[i]) {
  case CONSTANT_TERM:
  case UNINTERPRETED_TERM:
    pp_term_idx_name(printer, tbl, i, polarity);
    break;

  case BV64_CONSTANT:
    assert(polarity);
    pp_bvconst64_term(printer, tbl->desc[i].ptr);
    break;

  case BV_CONSTANT:
    assert(polarity);
    pp_bvconst_term(printer, tbl->desc[i].ptr);
    break;

  case OR_TERM:
    pp_or_term(printer, tbl, tbl->desc[i].ptr, level - 1, polarity);
    break;

  case EQ_TERM:
  case BV_EQ_ATOM:
    op = polarity ? PP_OPEN_EQ : PP_OPEN_NEQ;
    pp_binary_atom(printer, tbl, op, tbl->desc[i].ptr, level - 1);
    break;

  case BV_GE_ATOM:
    op = polarity ? PP_OPEN_BV_GE : PP_OPEN_BV_LT;
    pp_binary_atom(printer, tbl, op, tbl->desc[i].ptr, level - 1);
    break;

  case BV_SGE_ATOM:
    op = polarity ? PP_OPEN_BV_SGE : PP_OPEN_BV_SLT;
    pp_binary_atom(printer, tbl, op, tbl->desc[i].ptr, level - 1);
    break;

  case ITE_TERM:
  case DISTINCT_TERM:
  case XOR_TERM:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
    // i's descriptor is a composite term
    if (! polarity) pp_open_block(printer, PP_OPEN_NOT);
    pp_composite_term(printer, tbl, tbl->kind[i], tbl->desc[i].ptr, level - 1);
    if (! polarity) pp_close_block(printer, true);
    break;

  case BV_ARRAY:
    assert(polarity);
    pp_bvarray_term(printer, tbl, tbl->desc[i].ptr, level - 1);
    break;

  case BIT_TERM:
    if (!polarity) pp_open_block(printer, PP_OPEN_NOT);
    pp_select_term(printer, tbl, tbl->kind[i], &tbl->desc[i].select, level - 1);
    if (!polarity) pp_close_block(printer, true);
    break;

  case POWER_PRODUCT:
    assert(polarity);
    pp_pprod(printer, tbl, tbl->desc[i].ptr, level - 1);
    break;

  case BV64_POLY:
    assert(polarity);
    pp_bvpoly64(printer, tbl, tbl->desc[i].ptr, level - 1);
    break;

  case BV_POLY:
    assert(polarity);
    pp_bvpoly(printer, tbl, tbl->desc[i].ptr, level - 1);
    break;

  case UNUSED_TERM:
  case RESERVED_TERM:
  default:
    assert(false);
    break;
  }
}


/*
 * Print name of t if any. Otherwise, print ellipsis
 */
static void pp_name_if_any(yices_pp_t *printer, term_table_t *tbl, term_t t) {
  char *name;

  name = term_name(tbl, t);
  if (name != NULL) {
    pp_string(printer, name);
  } else {
    pp_string(printer, "...");
  }
}

// term t or (not t)
static void pp_term_recur(yices_pp_t *printer, term_table_t *tbl, term_t t, int32_t level, bool polarity) {
  int32_t i;

  assert(good_term(tbl, t));

  if (yices_pp_is_full(printer)) return;

  // convert to (not t) if polarity is false
  t = signed_term(t, polarity);

  if (t <= false_term) {
    pp_string(printer, (char *) term2string[t]);
  } else if (yices_pp_depth(printer) >= printer->pp.printer.area.width) {
    // heuristic to cut recursion for deep terms
    pp_name_if_any(printer, tbl, t);
  } else {
    i = index_of(t);
    pp_term_idx(printer, tbl, i, level, is_pos_term(t));
  }
}


/*
 * Expand top-level names
 */
void pp_term_exp(yices_pp_t *printer, term_table_t *tbl, term_t t) {
  pp_term_recur(printer, tbl, t, 1, true);
}


/*
 * Don't expand top-level names
 */
void pp_term(yices_pp_t *printer, term_table_t *tbl, term_t t) {
  pp_term_recur(printer, tbl, t, 0, true);
}


/*
 * Expand everything
 */
void pp_term_full(yices_pp_t *printer, term_table_t *tbl, term_t t) {
  pp_term_recur(printer, tbl, t, INT32_MAX, true);
}


/*
 * Term definition: same as pp_term_exp, except that uninterpreted constants,
 * variables, and constants of scalar types are treated differently.
 */
void pp_term_def(yices_pp_t *printer, term_table_t *tbl, term_t t) {
  assert(good_term(tbl, t));

  if (t <= false_term) {
    pp_string(printer, (char *) term2string[t]);
  } else {
    switch (term_kind(tbl, t)) {
    case CONSTANT_TERM:
      pp_open_block(printer, PP_OPEN_CONST_DEF);
      pp_int32(printer, constant_term_index(tbl, t));
      pp_string(printer, "of");
      pp_type(printer, tbl->types, term_type(tbl, t));
      pp_close_block(printer, true);
      break;

    case UNINTERPRETED_TERM:
      pp_open_block(printer, PP_OPEN_UNINT_DEF);
      pp_string(printer, "of");
      pp_type(printer, tbl->types, term_type(tbl, t));
      pp_close_block(printer, true);
      break;

    default:
      pp_term_exp(printer, tbl, t);
      break;
    }
  }
}


/*
 * Pretty print a term table
 */
void pp_term_table(FILE *f, term_table_t *tbl) {
  yices_pp_t printer;
  pp_area_t area;
  uint32_t i, n;
  uint32_t name_size;
  term_t t;
  term_kind_t kind;

  name_size = max_term_name_length(tbl) + 2;
  if (name_size < 4) {
    name_size = 4;
  } else if (name_size > 30) {
    name_size = 30;
  }

  area.width = 120;
  area.height = 6;
  area.offset = 14 + name_size;
  area.truncate = true;
  area.stretch = false;

  init_yices_pp(&printer, f, &area, PP_VMODE, 0);

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    kind = tbl->kind[i];
    if (kind != UNUSED_TERM && kind != RESERVED_TERM) {
      t = pos_term(i);
      fprintf(f, "term[%"PRId32"]: ", i);
      if (i < 10) fputc(' ', f);
      if (i < 100) fputc(' ', f);
      if (i < 1000) fputc(' ', f);
      if (i < 10000) fputc(' ', f);
      if (i < 100000) fputc(' ', f);
      print_padded_string(f, term_name(tbl, t), name_size);
      pp_term_def(&printer, tbl, t);
      flush_yices_pp(&printer);
    }
  }

  delete_yices_pp(&printer, false);
}


/*
 * More pretty printing
 */
static pp_area_t default_area = {
  120,        // width
  UINT32_MAX, // height
  0,          // offset
  false,      // stretch
  false       // truncate
};

void pretty_print_term_exp(FILE *f, pp_area_t *area, term_table_t *tbl, term_t t) {
  yices_pp_t printer;

  if (area == NULL) {
    area = &default_area;
  }
  init_yices_pp(&printer, f, area, PP_VMODE, 0);
  pp_term_exp(&printer, tbl, t);
  flush_yices_pp(&printer);
  delete_yices_pp(&printer, false);
}

void pretty_print_term_full(FILE *f, pp_area_t *area, term_table_t *tbl, term_t t) {
  yices_pp_t printer;

  if (area == NULL) {
    area = &default_area;
  }
  init_yices_pp(&printer, f, area, PP_VMODE, 0);
  pp_term_full(&printer, tbl, t);
  flush_yices_pp(&printer);
  delete_yices_pp(&printer, false);
}

