/*
 * Print terms and types and other internal objects
 * No pretty-printing. Can easily explode.
 */

#include <stdint.h>
#include <inttypes.h>

#include "yices_globals.h"
#include "term_printer.h"
#include "bitvectors.h"
#include "vsets.h"


/*
 * Provisional: set default visibility for functions used in test_smt_context
 */
#if defined(CYGWIN) || defined(MINGW)
#define EXPORTED __attribute__((dllexport))
#else
#define EXPORTED __attribute__((visibility("default")))
#endif



/*
 * Table: convert built-in bvops to strings
 */
static const char * const bvop2string[] = {
  "bv-div",
  "bv-rem",
  "bv-sdiv",
  "bv-srem",
  "bv-smod",
  "bv-shl",
  "bv-lshr",
  "bv-ashr",
};

static char bvbad_op[20];

static const char * bvop_name(uint32_t op) {
  if (op <= BVOP_ASHR) return bvop2string[op];
  
  sprintf(bvbad_op, "bv-op!%"PRIu32, op);
  return bvbad_op;
}

// arith-variable: x!i if it's a real, y!i if it's an integer
void print_arith_var(FILE *f, arith_var_t v) {
  if (arithvar_manager_var_is_int(__yices_globals.arith_manager, v)) {
    fprintf(f, "y!%"PRId32, v);
  } else {
    fprintf(f, "x!%"PRId32, v);
  }
}

// bitvector variable: u!i
void print_bv_var(FILE *f, bv_var_t v) {
  fprintf(f, "u!%"PRId32, v);
}

// term_id: t!i
EXPORTED
void print_term_id(FILE *f, term_t t) {
  fprintf(f, "t!%"PRId32, t);
}

// type_id: tau!i
void print_type_id(FILE *f, type_t tau) {
  fprintf(f, "tau!%"PRId32, tau);
}

// x!i^d
static void print_arith_varpower(FILE *f, varexp_t *p) {
  print_arith_var(f, p->var);
  if (p->exp > 1) {
    fprintf(f, "^%"PRId32, p->exp);
  }
}

static void print_bv_varpower(FILE *f, varexp_t *p) {
  print_bv_var(f, p->var);
  if (p->exp > 1) {
    fprintf(f, "^%"PRId32, p->exp);
  }
}

// varprod *p
void print_arith_varprod(FILE *f, varprod_t *p) {
  int32_t i, n;

  n = p->len;
  if (n == 0) {
    fprintf(f, "1"); // empty product
  } else {
    i = 0;
    for (;;) {
      print_arith_varpower(f, p->prod + i);
      i ++;
      if (i == n) break;
      fprintf(f, " * ");
    }
  }
}

void print_bv_varprod(FILE *f, varprod_t *p) {
  int32_t i, n;

  n = p->len;
  if (n == 0) {
    fprintf(f, "1"); // empty product
  } else {
    i = 0;
    for (;;) {
      print_bv_varpower(f, p->prod + i);
      i ++;
      if (i == n) break;
      fprintf(f, " * ");
    }
  }
}

// arithmetic variable x or expand it to a varprod
static void print_expand_arith_var(FILE *f, arith_var_t v) {
  polynomial_manager_t *m;

  m = &__yices_globals.arith_manager->pm;
  if (polymanager_var_is_primitive(m, v)) {
    print_arith_var(f, v);
  } else {
    print_arith_varprod(f, polymanager_var_product(m, v));
  }
}


// bitvector variable x or expand it to a varprod
static void print_expand_bv_var(FILE *f, arith_var_t v) {
  polynomial_manager_t *m;

  m = &__yices_globals.bv_manager->pm;
  if (polymanager_var_is_primitive(m, v)) {
    print_bv_var(f, v);
  } else {
    print_bv_varprod(f, polymanager_var_product(m, v));
  }
}

// monomial with rational coefficient
// first is true if this the first monomial in a polynomial
static void print_monomial(FILE *f, rational_t *coeff, arith_var_t v, bool first) {
  bool negative;
  bool abs_one;

  assert(q_is_nonzero(coeff));
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

  if (v == const_idx) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fprintf(f, " * ");
    }
    print_expand_arith_var(f, v);
  }
}


// polynomial p
void print_polynomial(FILE *f, polynomial_t *p) {
  int32_t i, n;

  n = p->nterms;
  if (n == 0) {
    fprintf(f, "0"); // zero polynomial
  } else {
    for (i=0; i<n; i++) {
      print_monomial(f, &p->mono[i].coeff, p->mono[i].var, i == 0);
    }
  }
}

// monomial array with end-marked = max_idx
void print_monarray(FILE *f, monomial_t *p) {
  arith_var_t x;

  x = p->var;
  if (x == max_idx) {
    fprintf(f, "0");
  } else {
    print_monomial(f, &p->coeff, x, true);
    for (;;) {
      p ++;
      x = p->var;
      if (x == max_idx) break;
      print_monomial(f, &p->coeff, x, false);
    }
  }
}


// buffer b.
void print_arith_buffer(FILE *f, arith_buffer_t *b) {
  mlist_t *p;
  arith_var_t v;

  if (b->nterms == 0) {
    fprintf(f, "0");
  } else {
    p = b->list->next;
    print_monomial(f, &p->coeff, p->var, true);
    p = p->next;
    v = p->var;
    while (v < max_idx) {
      print_monomial(f, &p->coeff, v, false);
      p = p->next;
      v = p->var;
    }
  }
}


// monomial with bitvector coefficient
// first is true if this the first monomial in a polynomial
// n = bitsize
static void print_bv_monomial(FILE *f, bvcoeff_t *a, uint32_t n, arith_var_t v, bool first) {
  uint32_t aux[2];

  if (! first) fprintf(f, " + ");

  if (n <= 64) {
    bvconst_set64(aux, 2, a->c);
    bvconst_print(f, aux, n);
  } else {
    bvconst_print(f, a->ptr, n);
  }
  if (v != const_idx) {
    fprintf(f, " * ");
    print_expand_bv_var(f, v);
  }
}


// polynomial p
void print_bvarith_expr(FILE *f, bvarith_expr_t *e) {
  int32_t i, n;
  uint32_t k;

  n = e->nterms;
  if (n == 0) {
    fprintf(f, "0"); // zero polynomial
  } else {
    k = e->size;
    for (i=0; i<n; i++) {
      print_bv_monomial(f, &e->mono[i].coeff, k, e->mono[i].var, i == 0);
    }
  }
}

// buffer b.
void print_bvarith_buffer(FILE *f, bvarith_buffer_t *b) {
  bvmlist_t *p;
  bv_var_t v;
  uint32_t k;

  if (b->nterms == 0) {
    fprintf(f, "0");
  } else {
    p = b->list->next;
    k = b->size;
    print_bv_monomial(f, &p->coeff, k, p->var, true);
    p = p->next;
    v = p->var;
    while (v < max_idx) {
      print_bv_monomial(f, &p->coeff, k, v, false);
      p = p->next;
      v = p->var;
    }
  }
}


/*
 * ARRAY OF BITS
 */
static void print_bit_expr_id(FILE *f, bit_t b) {
  if (b == true_bit) {
    fprintf(f, "tt");
  } else if (b == false_bit) {
    fprintf(f, "ff");
  } else {
    if (bit_is_neg(b)) fprintf(f, "~");
    fprintf(f, "b!%"PRId32, node_of_bit(b));
  }
}

static void print_bit_array(FILE *f, uint32_t n, bit_t *a) {
  uint32_t i;

  if (n == 0) fprintf(f, "[]");

  fprintf(f, "[");
  print_bit_expr_id(f, a[0]);
  for (i=1; i<n; i++) {
    fprintf(f, " ");
    print_bit_expr_id(f, a[i]);
  }
  fprintf(f, "]");
}

void print_bvlogic_expr(FILE *f, bvlogic_expr_t *e) {
  print_bit_array(f, e->nbits, e->bit);
}

void print_bvlogic_buffer(FILE *f, bvlogic_buffer_t *b) {
  print_bit_array(f, b->nbits, b->bit);
}




/*
 * NODES IN BIT EXPRESSIONS
 */
static void print_node_array(FILE *f, char *op, bit_t a[2]) {
  fprintf(f, "(%s ", op);
  print_bit_expr_id(f, a[0]);
  fprintf(f, " ");
  print_bit_expr_id(f, a[1]);
  fprintf(f, ")\n");
}

static void print_bit_node(FILE *f, node_t i) {
  int32_t x, k;

  fprintf(f, " b!%"PRId32": ", i);

  switch (node_kind(__yices_globals.nodes, i)) {
  case UNUSED_NODE:
    fprintf(f, "<unused>\n");
    break;

  case CONSTANT_NODE:
    fprintf(f, "<constant>\n");
    break;

  case VARIABLE_NODE:
    x = bv_var_of_node(__yices_globals.nodes, i);
    k = bv_var_manager_get_index_of_node(__yices_globals.bv_manager, x, pos_bit(i));
    print_bv_var(f, bv_var_of_node(__yices_globals.nodes, i));
    fprintf(f, "[%"PRId32"]\n", k);
    break;

  case OR_NODE:
    print_node_array(f, "OR", children_of_node(__yices_globals.nodes, i));
    break;

  case XOR_NODE:
    print_node_array(f, "XOR", children_of_node(__yices_globals.nodes, i));
    break;

  default:
    fprintf(f, "<ERROR>\n");
  }
}

void print_bit_expr(FILE *f, bit_t b) {
  int_hset_t set;
  uint32_t i, n;

  init_int_hset(&set, 0);
  collect_bitexpr_nodes(__yices_globals.nodes, b, &set);
  n = set.nelems;
  for (i=0; i<n; i++) {
    print_bit_node(f, set.data[i]);
  }
  delete_int_hset(&set);
}


/*
 * Print the bitvector variables occurring in bit b
 */
void print_vars_of_bit_expr(FILE *f, bit_t b) {
  vset_t *v;
  uint32_t i, n;

  v = vars_of_node(__yices_globals.nodes, node_of_bit(b));
  n = v->nelems;
  if (n == 0) {
    fputs("{}", f);
  } else {
    fputc('{', f);
    print_bv_var(f, v->data[0]);
    for (i=1; i<n; i++) {
      fputc(' ', f);
      print_bv_var(f, v->data[i]);
    }
    fputc('}', f);
  }
}


/*
 * Print type tau
 * if level == 0, do not expand type names.
 */
static void print_type_recur(FILE *f, type_table_t *table, type_t tau, int32_t level) {
  int32_t i;
  char *name;
  name = type_name(table, tau);
  if (name != NULL && level <= 0) {
    fprintf(f, "%s", name);
  } else {
    switch (type_kind(table, tau)) {
    case UNUSED_TYPE:
      fprintf(f, "dead-type!%"PRId32, tau);
      break;
    case BOOL_TYPE:
      fprintf(f, "bool");
      break;
    case INT_TYPE:
      fprintf(f, "int");
      break;
    case REAL_TYPE:
      fprintf(f, "real");
      break;
    case BITVECTOR_TYPE:
      fprintf(f, "(bitvector %"PRId32")", bv_type_size(table, tau));
      break;
    case SCALAR_TYPE:
      fprintf(f, "scalar-type!%"PRId32, tau);
      break;
    case UNINTERPRETED_TYPE:
      if (name != NULL) {
	fprintf(f, "%s", name);
      } else {
	fprintf(f, "unint-type!%"PRId32, tau);
      }
      break;
    case TUPLE_TYPE:
      fprintf(f, "(tuple");
      for (i=0; i<tuple_type_ncomponents(table, tau); i++) {
	fprintf(f, " ");
	print_type_recur(f, table, tuple_type_component(table, tau, i), level-1);
      }
      fprintf(f, ")");
      break;
    case FUNCTION_TYPE:
      fprintf(f, "(-> ");
      for (i=0; i<function_type_ndomains(table, tau); i++) {
	print_type_recur(f, table, function_type_domain(table, tau, i), level-1);
	fprintf(f, " ");
      }
      print_type_recur(f, table, function_type_range(table, tau), level-1);
      fprintf(f, ")");
      break;
    default:
      fprintf(f, "error-type!%"PRId32, tau);
      break;
    }
  }
}

void print_type(FILE *f, type_t tau) {
  if (tau == NULL_TYPE) {
    fputs("null_type", f);
  } else {
    print_type_recur(f, __yices_globals.types, tau, 0);
  }
}

void print_typedef(FILE *f, type_t tau) {
  if (tau == NULL_TYPE) {
    fputs("null_type", f);
  } else {
    print_type_recur(f, __yices_globals.types, tau, 1);
  }
}

void print_fulltype(FILE *f, type_t tau) {
  if (tau == NULL_TYPE) {
    fputs("null_type", f);
  } else {
    print_type_recur(f, __yices_globals.types, tau, 1000);
  }
}



/*
 * Print term t
 */
static void print_term_recur(FILE *f, term_table_t *table, term_t t, int32_t level) {
  int32_t i;
  char *name;
  term_t v;

  name = term_name(table, t);
  if (name != NULL && level <= 0 && term_kind(table, t) != CONSTANT_TERM) {
    fprintf(f, "%s", name);
  } else {
    switch (term_kind(table, t)) {
    case UNUSED_TERM:
      fprintf(f, "dead-term!%"PRId32, t);
      break;
    case CONSTANT_TERM:
      if (t == true_term_id) {
	fprintf(f, "true");
      } else if (t == false_term_id) {
	fprintf(f, "false");
      } else {
	fprintf(f, "k!%"PRId32, t);
      }
      break;
    case UNINTERPRETED_TERM:
      if (name != NULL) {
	fprintf(f, "%s", name);
      } else {
	fprintf(f, "t!%"PRId32, t);
      }
      break;
    case VARIABLE:
      fprintf(f, "v!%"PRId32, t);
      break;

    case NOT_TERM:
      fprintf(f, "(not ");
      print_term_recur(f, table, not_term_arg(table, t), level-1);
      fprintf(f, ")");
      break;
    case ITE_TERM:
      fprintf(f, "(ite ");
      print_term_recur(f, table, ite_term_cond(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, ite_term_then(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, ite_term_else(table, t), level-1);
      fprintf(f, ")");
      break;
    case EQ_TERM:
      fprintf(f, "(= ");
      print_term_recur(f, table, eq_term_left(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, eq_term_right(table, t), level-1);
      fprintf(f, ")");
      break;
    case APP_TERM:
      fprintf(f, "(");
      print_term_recur(f, table, app_term_fun(table, t), level-1);
      for (i=0; i<app_term_nargs(table, t); i++) {
	fprintf(f, " ");
	print_term_recur(f, table, app_term_arg(table, t, i), level-1);
      }
      fprintf(f, ")");
      break;
    case OR_TERM:
      fprintf(f, "(or");
      for (i=0; i<or_term_nargs(table, t); i++) {
	fprintf(f, " ");
	print_term_recur(f, table, or_term_arg(table, t, i), level-1);
      }
      fprintf(f, ")");	
      break;
    case TUPLE_TERM:
      fprintf(f, "(mk-tuple");
      for (i=0; i<tuple_term_nargs(table, t); i++) {
	fprintf(f, " ");
	print_term_recur(f, table, tuple_term_arg(table, t, i), level-1);
      }
      fprintf(f, ")");	
      break;
    case SELECT_TERM:
      fprintf(f, "(select ");
      print_term_recur(f, table, select_term_arg(table, t), level-1);
      fprintf(f, " %"PRId32")", select_term_index(table, t));
      break;

    case UPDATE_TERM:
      fprintf(f, "(update ");
      print_term_recur(f, table, update_term_fun(table, t), level-1);
      fprintf(f, " (");
      for (i=0; i<update_term_nargs(table, t); i++) {
	if (i>0) fprintf(f, " ");
	print_term_recur(f, table, update_term_arg(table, t, i), level-1);
      }
      fprintf(f, ") ");
      print_term_recur(f, table, update_term_newval(table, t), level-1);
      fprintf(f, ")");
      break;

    case DISTINCT_TERM:
      fprintf(f, "(distinct");
      for (i=0; i<distinct_term_nargs(table, t); i++) {
	fprintf(f, " ");
	print_term_recur(f, table, distinct_term_arg(table, t, i), level-1);
      }
      fprintf(f, ")");
      break;

    case FORALL_TERM:
      fprintf(f, "(forall (");
      for (i=0; i<forall_term_nvars(table, t); i++) {
	v = forall_term_var(table, t, i);
	if (i>0) fprintf(f, " ");
	print_term_recur(f, table, v, level-1);
	fprintf(f, "::");
	print_type_recur(f, table->type_table, term_type(table, v), level-1);
      }
      fprintf(f, ") ");
      print_term_recur(f, table, forall_term_body(table, t), level-1);
      fprintf(f, ")");
      break;

    case ARITH_TERM:
      print_polynomial(f, arith_term_desc(table, t));
      break;
    case ARITH_EQ_ATOM:
      fprintf(f, "(= (");
      print_polynomial(f, arith_atom_desc(table, t));
      fprintf(f, ") 0)");
      break;
    case ARITH_GE_ATOM:
      fprintf(f, "(>= (");
      print_polynomial(f, arith_atom_desc(table, t));
      fprintf(f, ") 0)");
      break;
    case ARITH_BINEQ_ATOM:
      fprintf(f, "(= ");
      print_term_recur(f, table, arith_bineq_left(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, arith_bineq_right(table, t), level-1);
      fprintf(f, ")");
      break;

    case BV_LOGIC_TERM:
      print_bvlogic_expr(f, bvlogic_term_desc(table, t));
      break;
    case BV_ARITH_TERM:
      print_bvarith_expr(f, bvarith_term_desc(table, t));
      break;
    case BV_CONST_TERM:
      bvconst_print(f, bvconst_term_value(table, t), bvconst_term_bitsize(table, t));
      break;
    case BV_EQ_ATOM:
      fprintf(f, "(bv-eq ");
      print_term_recur(f, table, bvatom_lhs(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, bvatom_rhs(table, t), level-1);
      fprintf(f, ")");
      break;
    case BV_GE_ATOM:
      fprintf(f, "(bv-ge ");
      print_term_recur(f, table, bvatom_lhs(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, bvatom_rhs(table, t), level-1);
      fprintf(f, ")");
      break;
    case BV_SGE_ATOM:
      fprintf(f, "(bv-sge ");
      print_term_recur(f, table, bvatom_lhs(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, bvatom_rhs(table, t), level-1);
      fprintf(f, ")");
      break;
    case BV_APPLY_TERM:
      fprintf(f, "(%s ", bvop_name(bvapply_term_op(table, t)));
      print_term_recur(f, table, bvapply_term_arg0(table, t), level-1);
      fprintf(f, " ");
      print_term_recur(f, table, bvapply_term_arg1(table, t), level-1);
      fprintf(f, ")");
      break;
    default:
      fprintf(f, "error-term!%"PRId32, t);
      break;
    }
  }
}


void print_term(FILE *f, term_t t) {
  print_term_recur(f, __yices_globals.terms, t, 0);
}

void print_termdef(FILE *f, term_t t) {
  print_term_recur(f, __yices_globals.terms, t, 1);
}

void print_fullterm(FILE *f, term_t t) {
  print_term_recur(f, __yices_globals.terms, t, 1000);
}


/*
 * Print type name or term name
 */
void print_type_name(FILE *f, type_t tau) {
  type_table_t *table;
  char *name;

  table = __yices_globals.types;
  name = type_name(table, tau);
  if (name != NULL) {
    fputs(name, f);
  } else {
    print_type_id(f, tau);
  }
}


void print_term_name(FILE *f, term_t t) {
  term_table_t *table;
  char *name;

  table = __yices_globals.terms;
  name = term_name(table, t);
  if (name != NULL) {
    fputs(name, f);
  } else {
    print_term_id(f, t);
  }
}



/*
 * Print details about type tau
 * 
 * For example:
 * type tau!k
 *   name: xxx
 *   def:  (tuple tau!k1 ... tau!kn)
 */
static void print_type_aux(FILE *f, type_table_t *table, type_t tau) {
  int32_t i;

  switch (type_kind(table, tau)) {
  case UNUSED_TYPE:
    fprintf(f, "dead\n");
    break;
  case BOOL_TYPE:
    fprintf(f, "bool\n");
    break;
  case INT_TYPE:
    fprintf(f, "int\n");
    break;
  case REAL_TYPE:
    fprintf(f, "real\n");
    break;
  case BITVECTOR_TYPE:
    fprintf(f, "(bitvector %"PRId32")\n", bv_type_size(table, tau));
    break;
  case SCALAR_TYPE:
    fprintf(f, "(scalar-type %"PRId32")\n", scalar_type_cardinal(table, tau));
    break;
  case UNINTERPRETED_TYPE:
    fprintf(f, "uninterpreted\n");
    break;
  case TUPLE_TYPE:
    fprintf(f, "(tuple");
    for (i=0; i<tuple_type_ncomponents(table, tau); i++) {
      fprintf(f, " tau!%"PRId32, tuple_type_component(table, tau, i));
    }
    fprintf(f, ")\n");
    break;
  case FUNCTION_TYPE:
    fprintf(f, "(->");
    for (i=0; i<function_type_ndomains(table, tau); i++) {
      fprintf(f, " tau!%"PRId32, function_type_domain(table, tau, i));
    }
    fprintf(f, " tau!%"PRId32")\n", function_type_range(table, tau));
    break;
  default:
    fprintf(f, "invalid\n");
    break;
  }
}

static void print_type_def(FILE *f, type_table_t *table, type_t tau) {
  char *name;

  fprintf(f, "type tau!%"PRId32"\n", tau);
  name = type_name(table, tau);
  if (name != NULL) fprintf(f, "  name: %s\n", name);

  fprintf(f, "  def:  ");
  print_type_aux(f, table, tau);
}

void print_type_data(FILE *f, type_t tau) {
  print_type_def(f, __yices_globals.types, tau);
}


/*
 * Print details about term t 
 */
// variant of print_term_id 
static void print_term_aux(FILE *f, term_table_t *table, term_t t) {
  char *name;
  term_kind_t kind;
  char prefix;

  name = term_name(table, t);
  if (name != NULL) {
    fprintf(f, "%s", name);
  } else {
    kind = term_kind(table, t);
    prefix = 't';
    if (kind == CONSTANT_TERM || kind == UNINTERPRETED_TERM) {
      //    prefix = 'k';
      prefix = 't';
    } else if (kind == VARIABLE) {
      prefix = 'v';
    }
    fprintf(f, "%c!%"PRId32, prefix, t);
  }
}

// print definition of t (non-recursive)
static void print_term_aux2(FILE *f, term_table_t *table, term_t t) {
  int32_t i;
  term_t v;

  switch (term_kind(table, t)) {
  case UNUSED_TERM:
    fprintf(f, "dead-term\n");
    break;

  case CONSTANT_TERM:
    if (t == true_term_id) {
      fprintf(f, "true\n"); 
    } else if (t == false_term_id) {
      fprintf(f, "false\n");
    } else {
      fprintf(f, "(const %"PRId32")\n", constant_term_index(table, t));
    }
    break;

  case UNINTERPRETED_TERM:
    fprintf(f, "unint: ");
    print_term_aux(f, table, t);
    fprintf(f, "\n");
    break;

  case VARIABLE:
    fprintf(f, "(var %"PRId32")\n", variable_index(table, t));
    break;

  case NOT_TERM:
    fprintf(f, "(not ");
    print_term_aux(f, table, not_term_arg(table, t));
    fprintf(f, ")\n");
    break;

  case ITE_TERM:
    fprintf(f, "(ite ");
    print_term_aux(f, table, ite_term_cond(table, t));
    fprintf(f, " ");
    print_term_aux(f, table, ite_term_then(table, t));
    fprintf(f, " ");
    print_term_aux(f, table, ite_term_else(table, t));
    fprintf(f, ")\n");
    break;

  case EQ_TERM:
    fprintf(f, "(= ");
    print_term_aux(f, table, eq_term_left(table, t));
    fprintf(f, " ");
    print_term_aux(f, table, eq_term_right(table, t));
    fprintf(f, ")\n");
    break;

  case APP_TERM:
    fprintf(f, "(");
    print_term_aux(f, table, app_term_fun(table, t));
    for (i=0; i<app_term_nargs(table, t); i++) {
      fprintf(f, " ");
      print_term_aux(f, table, app_term_arg(table, t, i));
    }
    fprintf(f, ")\n");
    break;

  case OR_TERM:
    fprintf(f, "(or");
    for (i=0; i<or_term_nargs(table, t); i++) {
      fprintf(f, " ");
      print_term_aux(f, table, or_term_arg(table, t, i));
    }
    fprintf(f, ")\n");	
    break;

  case TUPLE_TERM:
    fprintf(f, "(mk-tuple");
    for (i=0; i<tuple_term_nargs(table, t); i++) {
      fprintf(f, " ");
      print_term_aux(f, table, tuple_term_arg(table, t, i));
    }
    fprintf(f, ")\n");
    break;

  case SELECT_TERM:
    fprintf(f, "(select ");
    print_term_aux(f, table, select_term_arg(table, t));
    fprintf(f, " %"PRId32")\n", select_term_index(table, t));
    break;

  case UPDATE_TERM:
    fprintf(f, "(update ");
    print_term_aux(f, table, update_term_fun(table, t));
    fprintf(f, " (");
    for (i=0; i<update_term_nargs(table, t); i++) {
      if (i>0) fprintf(f, " ");
      print_term_aux(f, table, update_term_arg(table, t, i));
    }
    fprintf(f, ") ");
    print_term_aux(f, table, update_term_newval(table, t));
    fprintf(f, ")\n");
    break;

  case DISTINCT_TERM:
    fprintf(f, "(distinct");
    for (i=0; i<distinct_term_nargs(table, t); i++) {
      fprintf(f, " ");
      print_term_aux(f, table, distinct_term_arg(table, t, i));
    }
    fprintf(f, ")\n");
    break;

  case FORALL_TERM:
    fprintf(f, "(forall (");
    for (i=0; i<forall_term_nvars(table, t); i++) {
      v = forall_term_var(table, t, i);
      if (i>0) fprintf(f, " ");
      print_term_aux(f, table, v);
      fprintf(f, "::");
      print_type_id(f, term_type(table, v));
    }
    fprintf(f, ") ");
    print_term_aux(f, table, forall_term_body(table, t));
    fprintf(f, ")\n");
    break;

  case ARITH_TERM:
    print_polynomial(f, arith_term_desc(table, t));
    fprintf(f, "\n");
    break;

  case ARITH_EQ_ATOM:
    fprintf(f, "(= (");
    print_polynomial(f, arith_atom_desc(table, t));
    fprintf(f, ") 0)\n");
    break;

  case ARITH_GE_ATOM:
    fprintf(f, "(>= (");
    print_polynomial(f, arith_atom_desc(table, t));
    fprintf(f, ") 0)\n");
    break;

  case ARITH_BINEQ_ATOM:
    fprintf(f, "(= ");
    print_term_aux(f, table, arith_bineq_left(table, t));
    fprintf(f, " ");
    print_term_aux(f, table, arith_bineq_right(table, t));
    fprintf(f, ")\n");
    break;

  case BV_LOGIC_TERM:
    print_bvlogic_expr(f, bvlogic_term_desc(table, t));
    fprintf(f, "\n");
    break;

  case BV_ARITH_TERM:
    print_bvarith_expr(f, bvarith_term_desc(table, t));
    fprintf(f, "\n");
    break;

  case BV_CONST_TERM:
    bvconst_print(f, bvconst_term_value(table, t), bvconst_term_bitsize(table, t));
    fprintf(f, "\n");
    break;

  case BV_EQ_ATOM:
    fprintf(f, "(bv-eq ");
    print_term_aux(f, table, bvatom_lhs(table, t));
    fprintf(f, " ");
    print_term_aux(f, table, bvatom_rhs(table, t));
    fprintf(f, ")\n");
    break;

  case BV_GE_ATOM:
    fprintf(f, "(bv-ge ");
    print_term_aux(f, table, bvatom_lhs(table, t));
    fprintf(f, " ");
    print_term_aux(f, table, bvatom_rhs(table, t));
    fprintf(f, ")\n");
    break;

  case BV_SGE_ATOM:
    fprintf(f, "(bv-sge ");
    print_term_aux(f, table, bvatom_lhs(table, t));
    fprintf(f, " ");
    print_term_aux(f, table, bvatom_rhs(table, t));
    fprintf(f, ")\n");
    break;

    case BV_APPLY_TERM:
      fprintf(f, "(%s ", bvop_name(bvapply_term_op(table, t)));
      print_term_aux(f, table, bvapply_term_arg0(table, t));
      fprintf(f, " ");
      print_term_aux(f, table, bvapply_term_arg1(table, t));
      fprintf(f, ")\n");
      break;

  default:
    fprintf(f, "invalid\n");
    break;
  }
}

static void print_term_def(FILE *f, term_table_t *table, term_t t) {
  int32_t v;
  bit_t *a;
  char *name;

  fprintf(f, "term ");
  print_term_aux(f, table, t);
  fprintf(f, "\n");

  name = term_name(table, t);
  if (name != NULL) fprintf(f, "  name: %s\n", name);

  fprintf(f, "  type: tau!%"PRId32" = ", term_type(table, t));
  print_type_aux(f, table->type_table, term_type(table, t));

  fprintf(f, "  def:  ");
  print_term_aux2(f, table, t);

  v = term_theory_var(table, t);

  if (v != null_theory_var) {
    if (is_bitvector_term(table, t)) {      
      fprintf(f, "  th-var: ");
      print_bv_var(f, v);
      fprintf(f, "\n");
      a = bv_var_bit_array(table->bv_manager, v);
      if (a != NULL) {
	fprintf(f, "  bv-bridge: ");
	print_bit_array(f, term_bitsize(table, t), a);
	fprintf(f, "\n");
      }
    } else if (is_arithmetic_term(table, t)) {    
      fprintf(f, "  th-var: ");
      print_arith_var(f, v);
      fprintf(f, "\n");
    }
  }
}

void print_term_data(FILE *f, term_t t) {
  print_term_def(f, __yices_globals.terms, t);
}

void print_term_shallow(FILE *f, term_t t) {
  print_term_aux2(f, __yices_globals.terms, t);
}


/*
 * Print details about variables
 */
void print_bv_var_data(FILE *f, bv_var_t v) {  
  term_t t;
  bit_t *a;
  bv_var_manager_t *vm;

  vm = __yices_globals.bv_manager;

  fprintf(f, "bv-var u!%"PRId32"\n", v);
  fprintf(f, "  bitsize: %"PRIu32"\n", bv_var_bitsize(vm, v));

  if (polymanager_var_is_primitive(&vm->pm, v)) {
    fprintf(f, "  term: ");
    t = polymanager_var_index(&vm->pm, v);
    print_term_aux(f, __yices_globals.terms, t);
  } else {
    fprintf(f, "  def: ");
    print_bv_varprod(f, polymanager_var_product(&vm->pm, v));
  }
  fprintf(f, "\n");

  a = bv_var_bit_array(vm, v);
  if (a != NULL) {
    fprintf(f, "  bv-bridge: ");
    print_bit_array(f, bv_var_bitsize(vm, v), a);
    fprintf(f, "\n");
  }
}



void print_arith_var_data(FILE *f, arith_var_t v) {  
  term_t t;
  arithvar_manager_t *vm;

  vm = __yices_globals.arith_manager;

  fprintf(f, "arith-var ");
  print_arith_var(f, v);
  fprintf(f, "\n");

  if (polymanager_var_is_primitive(&vm->pm, v)) {
    fprintf(f, "  term: ");
    t = polymanager_var_index(&vm->pm, v);
    print_term_aux(f, __yices_globals.terms, t);
  } else {
    fprintf(f, "  def: ");
    print_arith_varprod(f, polymanager_var_product(&vm->pm, v));
  }
  fprintf(f, "\n");
}



/*
 * Print a term partition
 */
void print_epartition(FILE *f, epartition_t *p) {
  term_t *q, t;
  uint32_t i, n;

  n = p->nclasses;
  if (n == 0) {
    fprintf(f, "empty");
  } else {
    q = p->data;
    for (i=0; i<n; i++) {
      fprintf(f, " {");
      t = *q ++;
      while (t >= 0) {
	fputc(' ', f);
	print_term_name(f, t);	
	t = *q ++;
      }
      fprintf(f, " }");
    }
  }
}



/*
 * Print all the types
 */
static void print_type_table(FILE *f, type_table_t *tbl) {
  uint32_t i, n;

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (good_type(tbl, i)) {
      print_type_def(f, tbl, i);
    }
  }
}

EXPORTED
void print_all_types(FILE *f) {
  print_type_table(f, __yices_globals.types);
}


/*
 * Print all the terms
 */
static void print_term_table(FILE *f, term_table_t *tbl) {
  uint32_t i, n;

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (good_term(tbl, i)) {
      print_term_def(f, tbl, i);
    }
  }
}

EXPORTED
void print_all_terms(FILE *f) {
  print_term_table(f, __yices_globals.terms);
}



/*
 * Build mask of all variables in m's free list
 */
static byte_t *mask_dead_variables(polynomial_manager_t *m) {
  byte_t *mask;
  int32_t i, n;

  n = m->nelems;
  mask = allocate_bitvector(n);
  clear_bitvector(mask, n);

  i = m->free_idx;
  while (i >= 0) {
    set_bit(mask, i);
    i = m->desc[i].integer;
  }

  return mask;
}

/*
 * Data on all the bitvector variables
 */
void print_all_bv_vars(FILE *f) {
  bv_var_manager_t *m;
  int32_t i, n;
  byte_t *mask;

  m = __yices_globals.bv_manager;
  n = m->pm.nelems;
  mask = mask_dead_variables(&m->pm);

  for (i=0; i<n; i++) {
    if (! tst_bit(mask, i)) {
      print_bv_var_data(f, i);
    }
  }

  delete_bitvector(mask);
} 


/*
 * Data on all the arithmetic variables
 */
EXPORTED
void print_all_arith_vars(FILE *f) {
  arithvar_manager_t *m;
  int32_t i, n;
  byte_t *mask;

  m = __yices_globals.arith_manager;
  n = m->pm.nelems;
  mask = mask_dead_variables(&m->pm);

  for (i=0; i<n; i++) {
    if (! tst_bit(mask, i)) {
      print_arith_var_data(f, i);
    }
  }

  delete_bitvector(mask);
} 


/*
 * Print all root bit expressions
 */
static void print_root_bit_exprs(FILE *f, term_table_t *tbl) {
  uint32_t i, j, n;
  bvlogic_expr_t *e;

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (good_term(tbl, i) && term_kind(tbl, i) == BV_LOGIC_TERM) {
      e = bvlogic_term_desc(tbl, i);      
      for (j=0; j<e->nbits; j++) {
	if (! bit_is_const(e->bit[j])) {
	  fprintf(f, "\n---- bit %"PRIu32" of term ", j);
	  print_term_id(f, i);
	  fprintf(f, " ----\n");	  
	  fprintf(f, "vars: ");
	  print_vars_of_bit_expr(f, e->bit[j]);
	  fprintf(f, "\nDAG:\n");
	  print_bit_expr(f, e->bit[j]);
	  fprintf(f, "\n");
	}
      }
    }
  }
}

EXPORTED
void print_all_root_bit_exprs(FILE *f) {
  print_root_bit_exprs(f, __yices_globals.terms);
}



