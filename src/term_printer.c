/*
 * Print terms
 */

#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "bv64_constants.h"
#include "type_printer.h"
#include "term_printer.h"


/*
 * Provisional: set default visibility for functions used in test_smt_context
 */
#if defined(CYGWIN) || defined(MINGW)
#define EXPORTED __attribute__((dllexport))
#else
#define EXPORTED __attribute__((visibility("default")))
#endif


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

  if (t == false_term) {
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
    fputc(' ', f);
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
 * Polynomial
 */
static void print_monomial(FILE *f, rational_t *coeff, int32_t x, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      fprintf(f, "- ");     
    } else {
      fprintf(f, " - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fprintf(f, " + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (x == const_idx) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fprintf(f, " ");
    }
    print_term_id(f, x);
  }  
}


void print_polynomial(FILE *f, polynomial_t *p) {
  uint32_t i, n;
  bool first;

  if (polynomial_is_zero(p)) {
    fputc('0', f);
  } else {
    n = p->nterms;
    first = true;
    for (i=0; i<n; i++) {
      print_monomial(f, &p->mono[i].coeff, p->mono[i].var, first);
      first = false;
    }
  }
}


/*
 * Arithmetic buffer
 */
static void print_arith_monomial(FILE *f, rational_t *coeff, pprod_t *r, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      fprintf(f, "- ");     
    } else {
      fprintf(f, " - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fprintf(f, " + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (pp_is_empty(r)) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fprintf(f, " ");
    }
    print_pprod(f, r);
  }

}


void print_arith_buffer(FILE *f, arith_buffer_t *b) {
  mlist_t *p;
  bool first;

  if (arith_buffer_is_zero(b)) {
    fprintf(f, "0");
  } else {
    p = b->list;
    first = true;
    while (p->next != NULL) {
      print_arith_monomial(f, &p->coeff, p->prod, first);
      first = false;
      p = p->next;
    }
  }
}


/*
 * Bit-vector polynomial
 */
static void print_bvmono(FILE *f, uint32_t *coeff, int32_t x, uint32_t n, bool first) {
  if (! first) {
    fputs(" + ", f);
  }

  bvconst_print(f, coeff, n);
  if (x != const_idx) {
    fputc(' ', f);
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
  if (! first) {
    fprintf(f, " + ");
  }
  bvconst_print(f, coeff, n);
  if (! pp_is_empty(r)) {
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
 * Bit-vector polynomial, small coeffcients
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
  if (! first) {
    fputs(" + ", f);
  }

  print_bvconst64(f, coeff, n);
  if (x != const_idx) {
    fputc(' ', f);
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
  if (! first) {
    fprintf(f, " + ");
  }
  print_bvconst64(f, coeff, n);
  if (! pp_is_empty(r)) {
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
static const char * const tag2string[] = {
  "unused",
  "reserved",
  "constant",
  "uninterpreted",
  "variable"
  "ite",
  "", // function application
  "update",
  "tuple",
  "select",
  "eq",
  "distinct",
  "forall",
  "or",
  "xor",
  "bit",
  "pprod",
  "arith-const",
  "arith-poly",
  "arith-eq-atom",
  "arith-ge-atom",
  "arith-bineq-atom",
  "bv64-const",
  "bv-const",
  "bv64-poly",
  "bv-poly",
  "bv-array",  
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
};



/*
 * Recusively print term t: if level <= 0, don't expand term that have a name
 */
static void print_term_recur(FILE *f, term_table_t *tbl, term_t t, int32_t level);

// generic composite
static void print_composite_term(FILE *f, term_table_t *tbl, term_kind_t tag, composite_term_t *d, int32_t level) {
  uint32_t i, n;

  assert(0 <= tag && tag <= BV_SGE_ATOM);
  fputc('(', f);
  fputs(tag2string[tag], f);
  n = d->arity;
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_term_recur(f, tbl, d->arg[i], level);
  }
  fputc(')', f);
}

// select
static void print_select_term(FILE *f, term_table_t *tbl, term_kind_t tag, select_term_t *d, int32_t level) {
  assert(0 <= tag && tag <= BV_SGE_ATOM);
  fprintf(f, "(%s %"PRIu32, tag2string[tag], d->idx);
  print_term_recur(f, tbl, d->arg, level);
  fputc(')', f);
}

// polynomial
static void print_mono_recur(FILE *f, term_table_t *tbl, rational_t *coeff, int32_t x, bool first, int32_t level) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      fprintf(f, "- ");     
    } else {
      fprintf(f, " - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fprintf(f, " + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (x == const_idx) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fprintf(f, " ");
    }
    print_term_recur(f, tbl, x, level);
  }  
}

static void print_polynomial_term(FILE *f, term_table_t *tbl, polynomial_t *p, int32_t level) {
  uint32_t i, n;
  bool first;

  if (polynomial_is_zero(p)) {
    fputc('0', f);
  } else {
    n = p->nterms;
    first = true;
    for (i=0; i<n; i++) {
      print_mono_recur(f, tbl, &p->mono[i].coeff, p->mono[i].var, first, level);
      first = false;
    }
  }
}

// bitvector polynomial
static void print_bvmono_recur(FILE *f, term_table_t *tbl, uint32_t *coeff, int32_t x, uint32_t n, bool first, int32_t level) {
  if (! first) {
    fputs(" + ", f);
  }

  bvconst_print(f, coeff, n);
  if (x != const_idx) {
    fputc(' ', f);
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
  if (! first) {
    fputs(" + ", f);
  }

  print_bvconst64(f, coeff, n);
  if (x != const_idx) {
    fputc(' ', f);
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
    fputc(' ', f);
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

static void print_term_recur(FILE *f, term_table_t *tbl, term_t t, int32_t level) {
  char *name;
  int32_t i;

  if (t <= false_term) {
    fputs(term2string[t], f);
  } else {
    name = term_name(tbl, t);
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      if (is_neg_term(t)) fputs("(not ", f);
      i = index_of(t);

      switch (tbl->kind[i]) {
      case CONSTANT_TERM:
	fprintf(f, "(const %"PRId32" of type ", tbl->desc[i].integer);
	print_type_name(f, tbl->types, tbl->type[i]);
	fputc(')', f);
	break;

      case UNINTERPRETED_TERM:
	fprintf(f, "(unint of type ");
	print_type_id(f, tbl->type[i]);
	fputc(')', f);
	break;

      case VARIABLE:
	fprintf(f, "(var %"PRId32" of type ", tbl->desc[i].integer);
	print_type_name(f, tbl->types, tbl->type[i]);
	fputc(')', f);
	break;

      case ARITH_CONSTANT:
	q_print(f, &tbl->desc[i].rational);
	break;

      case BV64_CONSTANT:
	print_bvconst64_term(f, tbl->desc[i].ptr);
	break;

      case BV_CONSTANT:
	print_bvconst_term(f, tbl->desc[i].ptr);
	break;

      case ARITH_EQ_ATOM:
	fputs("(arith-eq ", f);
	print_term_recur(f, tbl, tbl->desc[i].integer, level - 1);
	fputs(" 0)", f);
	break;

      case ARITH_GE_ATOM:
	fputs("(arith-ge ", f);
	print_term_recur(f, tbl, tbl->desc[i].integer, level - 1);
	fputs(" 0)", f);
	break;

      case ITE_TERM:
      case APP_TERM:
      case UPDATE_TERM:
      case TUPLE_TERM:
      case EQ_TERM:
      case DISTINCT_TERM:
      case FORALL_TERM:
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
	print_composite_term(f, tbl, tbl->kind[i], tbl->desc[i].ptr, level - 1);
	break;

      case SELECT_TERM:
      case BIT_TERM:
	print_select_term(f, tbl, tbl->kind[i], tbl->desc[i].ptr, level - 1);
	break;

      case POWER_PRODUCT:
	print_power_product_term(f, tbl, tbl->desc[i].ptr, level - 1);
	break;

      case ARITH_POLY:
	print_polynomial_term(f, tbl, tbl->desc[i].ptr, level - 1);
	break;

      case BV64_POLY:
	print_bvpoly64_term(f, tbl, tbl->desc[i].ptr, level - 1);
	break;

      case BV_POLY:
	print_bvpoly_term(f, tbl, tbl->desc[i].ptr, level - 1);
	break;

      case UNUSED_TERM:
      case RESERVED_TERM:
      default:
	fprintf(f, "bad-term-%"PRIu32, i);
	break;
      }

      if (is_neg_term(t)) fputc(')', f);
    }
  }
}


/*
 * Print term t: expand names at the outer level only
 */
void print_term(FILE *f, term_table_t *tbl, term_t t) {
  print_term_recur(f, tbl, t, 1);
}


/*
 * Term definition: name := expr
 */
void print_term_def(FILE *f, term_table_t *tbl, term_t t) {
  print_term_name(f, tbl, t);
  fputs(" := ", f);
  print_term_recur(f, tbl, t, 1);
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
    if (tbl->kind[i] != UNUSED_TYPE) {
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
static void print_composite(FILE *f, term_kind_t tag, composite_term_t *d) {
  uint32_t i, n;

  assert(0 <= tag && tag <= BV_SGE_ATOM);
  fputc('(', f);
  fputs(tag2string[tag], f);
  n = d->arity;
  for (i=0; i<n; i++) {
    fputc(' ', f);
    print_term_id(f, d->arg[i]);
  }
  fputc(')', f);
}

// select
static void print_select(FILE *f, term_kind_t tag, select_term_t *d) {
  assert(0 <= tag && tag <= BV_SGE_ATOM);
  fprintf(f, "(%s %"PRIu32, tag2string[tag], d->idx);
  print_term_id(f, d->arg);
  fputc(')', f);
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
      fprintf(f, "%4"PRIu32, i);
      print_padded_string(f, term_name(tbl, pos_term(i)), name_size);

      // definition
      switch (tbl->kind[i]) {
      case CONSTANT_TERM:
	fprintf(f, "(const %"PRId32" of type ", tbl->desc[i].integer);
	print_type_name(f, tbl->types, tbl->type[i]);
	fputc(')', f);
	break;

      case UNINTERPRETED_TERM:
	fprintf(f, "(unint of type ");
	print_type_id(f, tbl->type[i]);
	fputc(')', f);
	break;

      case VARIABLE:
	fprintf(f, "(var %"PRId32" of type ", tbl->desc[i].integer);
	print_type_name(f, tbl->types, tbl->type[i]);
	fputc(')', f);
	break;

      case ARITH_CONSTANT:
	q_print(f, &tbl->desc[i].rational);
	break;

      case BV64_CONSTANT:
	print_bvconst64_term(f, tbl->desc[i].ptr);
	break;

      case BV_CONSTANT:
	print_bvconst_term(f, tbl->desc[i].ptr);
	break;

      case ARITH_EQ_ATOM:
	fputs("(arith-eq ", f);
	print_term_id(f, tbl->desc[i].integer);
	fputs(" 0)", f);
	break;

      case ARITH_GE_ATOM:
	fputs("(arith-ge ", f);
	print_term_id(f, tbl->desc[i].integer);
	fputs(" 0)", f);
	break;

      case ITE_TERM:
      case APP_TERM:
      case UPDATE_TERM:
      case TUPLE_TERM:
      case EQ_TERM:
      case DISTINCT_TERM:
      case FORALL_TERM:
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
	print_composite(f, tbl->kind[i], tbl->desc[i].ptr);
	break;

      case SELECT_TERM:
      case BIT_TERM:
	print_select(f, tbl->kind[i], tbl->desc[i].ptr);
	break;

      case POWER_PRODUCT:
	print_pprod(f, tbl->desc[i].ptr);
	break;

      case ARITH_POLY:
	print_polynomial(f, tbl->desc[i].ptr);
	break;

      case BV64_POLY:
	print_bvpoly64(f, tbl->desc[i].ptr);
	break;

      case BV_POLY:
	print_bvpoly(f, tbl->desc[i].ptr);
	break;

      case UNUSED_TERM:
      case RESERVED_TERM:
      default:
	fprintf(f, "bad-term-%"PRIu32, i);
	break;
      }

      fputc('\n', f);
    }
  }
}
