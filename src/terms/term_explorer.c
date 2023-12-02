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

#include <assert.h>

#include "terms/bv64_constants.h"
#include "terms/term_explorer.h"


/*
 * Tables indexed by term_kind (defined in terms.h)
 */
static const uint8_t atomic_term_flag[NUM_TERM_KINDS] = {
  false, // UNUSED_TERM
  false, // RESERVED_TERM
  true,  // CONSTANT_TERM
  true,  // ARITH_CONSTANT
  true,  // ARITH_FF_CONSTANT
  true,  // BV64_CONSTANT
  true,  // BV_CONSTANT
  true,  // VARIABLE
  true,  // UNINTERPRETED_TERM
  false, // ARITH_EQ_ATOM
  false, // ARITH_GE_ATOM
  false, // ARITH_IS_INT_ATOM
  false, // ARITH_FLOOR
  false, // ARITH_CEIL
  false, // ARITH_ABS
  false, // ARITH_ROOT_ATOM
  false, // ARITH_FF_EQ_ATOM
  false, // ITE_TERM
  false, // ITE_SPECIAL
  false, // APP_TERM
  false, // UPDATE_TERM
  false, // TUPLE_TERM
  false, // EQ_TERM
  false, // DISTINCT_TERM
  false, // FORALL_TERM
  false, // LAMBDA_TERM
  false, // OR_TERM
  false, // XOR_TERM
  false, // ARITH_BINEQ_ATOM
  false, // ARITH_RDIV
  false, // ARITH_IDIV
  false, // ARITH_MOD
  false, // ARITH_DIVIDES
  false, // ARITH_FF_BINEQ_ATOM
  false, // BV_ARRAY
  false, // BV_DIV
  false, // BV_REM
  false, // BV_SDIV
  false, // BV_SREM
  false, // BV_SMOD
  false, // BV_SHL
  false, // BV_LSHR
  false, // BV_ASHR
  false, // BV_EQ_ATOM
  false, // BV_GE_ATOM
  false, // BV_SGE_ATOM
  false, // SELECT_TERM
  false, // BIT_TERM
  false, // POWER_PRODUCT
  false, // ARITH_POLY
  false, // ARITH_FF_POLY
  false, // BV64_POLY
  false, // BV_POLY
};

static const uint8_t composite_term_flag[NUM_TERM_KINDS] = {
  false, // UNUSED_TERM
  false, // RESERVED_TERM
  false, // CONSTANT_TERM
  false, // ARITH_CONSTANT
  false, // ARITH_FF_CONSTANT
  false, // BV64_CONSTANT
  false, // BV_CONSTANT
  false, // VARIABLE
  false, // UNINTERPRETED_TERM
  true,  // ARITH_EQ_ATOM
  true,  // ARITH_GE_ATOM
  true,  // ARITH_IS_INT_ATOM
  true,  // ARITH_FLOOR
  true,  // ARITH_CEIL
  true,  // ARITH_ABS
  true,  // ARITH_ROOT_ATOM
  true,  // ARITH_FF_EQ_ATOM
  true,  // ITE_TERM
  true,  // ITE_SPECIAL
  true,  // APP_TERM
  true,  // UPDATE_TERM
  true,  // TUPLE_TERM
  true,  // EQ_TERM
  true,  // DISTINCT_TERM
  true,  // FORALL_TERM
  true,  // LAMBDA_TERM
  true,  // OR_TERM
  true,  // XOR_TERM
  true,  // ARITH_BINEQ_ATOM
  true,  // ARITH_RDIV
  true,  // ARITH_IDIV
  true,  // ARITH_MOD
  true,  // ARITH_DIVIDES
  true,  // ARITH_FF_BINEQ_ATOM
  true,  // BV_ARRAY
  true,  // BV_DIV
  true,  // BV_REM
  true,  // BV_SDIV
  true,  // BV_SREM
  true,  // BV_SMOD
  true,  // BV_SHL
  true,  // BV_LSHR
  true,  // BV_ASHR
  true,  // BV_EQ_ATOM
  true,  // BV_GE_ATOM
  true,  // BV_SGE_ATOM
  false, // SELECT_TERM
  false, // BIT_TERM
  false, // POWER_PRODUCT
  false, // ARITH_POLY
  false, // ARITH_FF_POLY
  false, // BV64_POLY
  false, // BV_POLY
};

// term_kind --> term_constructor
static const term_constructor_t constructor_term_table[NUM_TERM_KINDS] = {
  YICES_CONSTRUCTOR_ERROR,  // UNUSED_TERM
  YICES_CONSTRUCTOR_ERROR,  // RESERVED_TERM
  YICES_SCALAR_CONSTANT,    // CONSTANT_TERM
  YICES_ARITH_CONSTANT,     // ARITH_CONSTANT
  YICES_ARITH_FF_CONSTANT,  // ARITH_FF_CONSTANT
  YICES_BV_CONSTANT,        // BV64_CONSTANT
  YICES_BV_CONSTANT,        // BV_CONSTANT
  YICES_VARIABLE,           // VARIABLE
  YICES_UNINTERPRETED_TERM, // UNINTERPRETED_TERM
  YICES_EQ_TERM,            // ARITH_EQ_ATOM
  YICES_ARITH_GE_ATOM,      // ARITH_GE_ATOM
  YICES_IS_INT_ATOM,        // ARITH_IS_INT_ATOM
  YICES_FLOOR,              // ARITH_FLOOR
  YICES_CEIL,               // ARITH_CEIL
  YICES_ABS,                // ARITH_ABS
  YICES_ARITH_ROOT_ATOM,    // ARITH_ROOT_ATOM
  YICES_EQ_TERM,            // ARITH_FF_EQ_ATOM
  YICES_ITE_TERM,           // ITE_TERM
  YICES_ITE_TERM,           // ITE_SPECIAL
  YICES_APP_TERM,           // APP_TERM
  YICES_UPDATE_TERM,        // UPDATE_TERM
  YICES_TUPLE_TERM,         // TUPLE_TERM
  YICES_EQ_TERM,            // EQ_TERM
  YICES_DISTINCT_TERM,      // DISTINCT_TERM
  YICES_FORALL_TERM,        // FORALL_TERM
  YICES_LAMBDA_TERM,        // LAMBDA_TERM
  YICES_OR_TERM,            // OR_TERM
  YICES_XOR_TERM,           // XOR_TERM
  YICES_EQ_TERM,            // ARITH_BINEQ_ATOM
  YICES_RDIV,               // ARITH_RDIV
  YICES_IDIV,               // ARITH_IDIV
  YICES_IMOD,               // ARITH_MOD
  YICES_DIVIDES_ATOM,       // ARITH_DIVIDES_ATOM
  YICES_EQ_TERM,            // ARITH_FF_BINEQ_ATOM
  YICES_BV_ARRAY,           // BV_ARRAY
  YICES_BV_DIV,             // BV_DIV
  YICES_BV_REM,             // BV_REM
  YICES_BV_SDIV,            // BV_SDIV
  YICES_BV_SREM,            // BV_SREM
  YICES_BV_SMOD,            // BV_SMOD
  YICES_BV_SHL,             // BV_SHL
  YICES_BV_LSHR,            // BV_LSHR
  YICES_BV_ASHR,            // BV_ASHR
  YICES_EQ_TERM,            // BV_EQ_ATOM
  YICES_BV_GE_ATOM,         // BV_GE_ATOM
  YICES_BV_SGE_ATOM,        // BV_SGE_ATOM
  YICES_SELECT_TERM,        // SELECT_TERM
  YICES_BIT_TERM,           // BIT_TERM
  YICES_POWER_PRODUCT,      // POWER_PRODUCT
  YICES_ARITH_SUM,          // ARITH_POLY
  YICES_ARITH_FF_SUM,       // ARITH_FF_POLY
  YICES_BV_SUM,             // BV64_POLY
  YICES_BV_SUM,             // BV_POLY
};


/*
 * Check the class of term t
 * - t must be a valid term in table
 * 
 * Note: negative terms are composite, except false_term
 */
bool term_is_atomic(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(good_term(table, t));

  if (index_of(t) == bool_const) {
    assert(t == false_term || t == true_term);
    return true;
  }

  kind = term_kind(table, t);
  return is_pos_term(t) && atomic_term_flag[kind];
}

bool term_is_composite(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(good_term(table, t));

  if (index_of(t) == bool_const) {
    assert(t == false_term || t == true_term);
    return false;
  }

  kind = term_kind(table, t);
  return is_neg_term(t) || composite_term_flag[kind];
}

bool term_is_projection(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(good_term(table, t));

  kind = term_kind(table, t);
  return is_pos_term(t) && (kind == SELECT_TERM || kind == BIT_TERM);
}

bool term_is_sum(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(good_term(table, t));

  kind = term_kind(table, t);
  return is_pos_term(t) && kind == ARITH_POLY;
}

bool term_is_bvsum(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(good_term(table, t));

  kind = term_kind(table, t);
  return is_pos_term(t) && (kind == BV_POLY || kind == BV64_POLY);
}

bool term_is_product(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(good_term(table, t));

  kind = term_kind(table, t);
  return is_pos_term(t) && kind == POWER_PRODUCT;
}


/*
 * Constructor code for term t
 * - t must be valid in table
 * - the constructor codes are defined in yices_types.h
 */
term_constructor_t term_constructor(term_table_t *table, term_t t) {
  term_kind_t kind;
  term_constructor_t result;

  assert(good_term(table, t));

  if (index_of(t) == bool_const) {
    assert(t == false_term || t == true_term);
    result = YICES_BOOL_CONSTANT;
  } else if (is_neg_term(t)) {
    result = YICES_NOT_TERM;
  } else {
    kind = term_kind(table, t);
    result = constructor_term_table[kind];
  }

  return result;
}


/*
 * Number of children of t (this is no more than YICES_MAX_ARITY)
 * - for a sum, this returns the number of summands
 * - for a product, this returns the number of factors
 */
uint32_t term_num_children(term_table_t *table, term_t t) {
  uint32_t result;

  assert(good_term(table, t));

  result = 0; // prevents bogus GCC warning

  if (index_of(t) == bool_const) {
    assert(t == false_term || t == true_term);
    result = 0;
  } else if (is_neg_term(t)) {
    result = 1;
  } else {

    switch (term_kind(table, t)) {
    case UNUSED_TERM:   // should not happen
    case RESERVED_TERM: // should not happen either
      assert(false);    // fall through to prevent compile-time warning
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case ARITH_FF_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
    case VARIABLE:
    case UNINTERPRETED_TERM:
      result = 0;
      break;

    case ARITH_EQ_ATOM:
    case ARITH_FF_EQ_ATOM:
    case ARITH_GE_ATOM:
      // internally, these are terms of the form t==0 or t >= 0
      // to be uniform, we report them as binary operators
      result = 2;
      break;

    case ARITH_ROOT_ATOM:
      // internally, these are terms of the form x r p for root index k
      // to be uniform, we report them as binary operators
      result = 2;
      break;

    case ARITH_IS_INT_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
      result = 1;
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case FORALL_TERM:
    case LAMBDA_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    case ARITH_DIVIDES_ATOM:
    case ARITH_FF_BINEQ_ATOM:
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
      result = composite_term_arity(table, t);      
      break;

    case SELECT_TERM:
    case BIT_TERM:
      result = 1;
      break;

    case POWER_PRODUCT:
      result = pprod_term_desc(table, t)->len;
      break;

    case ARITH_POLY:
      result = poly_term_desc(table, t)->nterms;
      break;      

    case ARITH_FF_POLY:
      result = finitefield_poly_term_desc(table, t)->nterms;
      break;

    case BV64_POLY:
      result = bvpoly64_term_desc(table, t)->nterms;
      break;

    case BV_POLY:
      result = bvpoly_term_desc(table, t)->nterms;
      break;
    }
  }

  return result;
}


/*
 * First and second child of a root atom
 *
 * Internally, a root atom is of the form  (x r root(k, p)) for root index k
 * - where both x and p are terms
 * - r is an binary comparison (i.e., ==, <, <=, >=, >, !=)
 * - k is an index
 *
 * We return x as first child and p as second child
 */
static term_t arith_root_atom_child(const root_atom_t *a, uint32_t i) {
  assert(a != NULL && i < 2);
  return (i == 0) ? a->x : a->p;
}

/*
 * i-th child of term t:
 * - t must be valid term in table
 * - t must be a composite term
 * - if n is term_num_children(table, t) then i must be in [0 ... n-1]
 */
term_t term_child(term_table_t *table, term_t t, uint32_t i) {
  term_t result;

  assert(term_is_composite(table, t) && i < term_num_children(table, t));

  if (is_neg_term(t)) {
    assert(i == 0);
    result = opposite_term(t); // (not t)
  } else {
    switch (term_kind(table, t)) {
    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      assert(i < 2);
      if (i == 0) {
	result = arith_atom_arg(table, t);
      } else {
	result = zero_term; // second child is always zero
      }
      break;

    case ARITH_IS_INT_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
      assert(i == 0);
      result = unary_term_arg(table, t);
      break;

    case ARITH_ROOT_ATOM:
      // internally, these are terms of the form x r p for root index k
      // to be uniform, we report them as binary operators
      // x is the first child
      // p is the second child
      result = arith_root_atom_child(arith_root_atom_desc(table, t), i);
      break;

    default:
      result = composite_term_arg(table, t, i);
      break;
    }
  }

  return result;
}


/*
 * All children of t:
 * - t must be a valid term in table
 * - t must be a composite term
 *.- the children of t are added to vector v
 */
void get_term_children(term_table_t *table, term_t t, ivector_t *v) {
  root_atom_t *a;
  composite_term_t *c;
  uint32_t i, n;

  assert(term_is_composite(table, t));

  if (is_neg_term(t)) {
    ivector_push(v, opposite_term(t)); // not(t)
  } else {
    switch (term_kind(table, t)) {
    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      // t == 0 or t >= 0
      // treat them like binary terms
      ivector_push(v, arith_atom_arg(table, t));
      ivector_push(v, zero_term);
      break;

    case ARITH_IS_INT_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
      ivector_push(v, unary_term_arg(table, t));
      break;

    case ARITH_ROOT_ATOM:
      a = arith_root_atom_desc(table, t);
      ivector_push(v, a->x); // a->x == child 0
      ivector_push(v, a->p); // a->p == child 1
      break;

    default:
      c = composite_term_desc(table, t);
      n = c->arity;
      for (i=0; i<n; i++) {
	ivector_push(v, c->arg[i]);
      }
      break;
    }
  }
}



/*
 * Components of a projection
 * - t must be a valid term in table and it must be either a SELECT_TERM
 *   or a BIT_TERM
 */
int32_t proj_term_index(term_table_t *table, term_t t) {
  assert(term_is_projection(table, t));
  return select_for_idx(table, index_of(t))->idx;
}

term_t proj_term_arg(term_table_t *table, term_t t) {
  assert(term_is_projection(table, t));
  return select_for_idx(table, index_of(t))->arg;
}

/*
 * Components of an arithmetic sum
 * - t must be a valid ARITH_POLY term in table
 * - i must be an index in [0 ... n-1] where n = term_num_children(table, t)
 * - the component is a pair (coeff, child): coeff is copied into q
 * - q must be initialized
 */
void sum_term_component(term_table_t *table, term_t t, uint32_t i, mpq_t q, term_t *child) {
  polynomial_t *p;
  term_t v;

  assert(is_pos_term(t) && term_kind(table, t) == ARITH_POLY);
  p = poly_term_desc(table, t);
  assert(i < p->nterms);

  v = p->mono[i].var;
  if (v == const_idx) {
    v = NULL_TERM;
  }
  *child = v;
  q_get_mpq(&p->mono[i].coeff, q);
}


/*
 * Components of a bitvector sum
 * - t must be a valid BV_POLY or BV64_POLY term in table
 * - i must be an index in [0 ... n-1] where n = term_num_children(table, t)
 * - the component is a pair (coeff, child):
 *   coeff is a bitvector constant
 *   child is a bitvector term 
 * The coeff is returned in array a
 * - a must be large enough to store nbits integers, where nbits = number of bits in t
 *   a[0] = lower order bit of the constant
 *   a[nbits-1] = higher order bit
 */
void bvsum_term_component(term_table_t *table, term_t t, uint32_t i, int32_t a[], term_t *child) {
  bvpoly_t *p;
  bvpoly64_t *q;
  term_t v;

  assert(is_pos_term(t));

  switch (term_kind(table, t)) {
  case BV64_POLY:
    q = bvpoly64_term_desc(table, t);
    assert(i < q->nterms);
    v = q->mono[i].var;
    if (v == const_idx) {
      v = NULL_TERM;
    }
    *child = v;
    bvconst64_get_array(q->mono[i].coeff, a, q->bitsize);
    break;

  case BV_POLY:
    p = bvpoly_term_desc(table, t);
    assert(i < p->nterms);
    v = p->mono[i].var;
    if (v == const_idx) {
      v = NULL_TERM;
    }
    *child = v;
    bvconst_get_array(p->mono[i].coeff, a, p->bitsize);    
    break;

  default:
    assert(false);
    break;
  }
}


/*
 * Components of a power-product
 * - t must be a valid POWER_PRODUCT term in table
 * - i must be an index in [0 .. n-1] where n = term_num_children(table, t)
 * - the component is a pair (child, exponent)
 *   child is a term (arithmetic or bitvector term)
 *   exponent is a positive integer
 */
void product_term_component(term_table_t *table, term_t t, uint32_t i, term_t *child, uint32_t *exp) {
  pprod_t *p;

  assert(is_pos_term(t) && term_kind(table, t) == POWER_PRODUCT);
  p = pprod_term_desc(table, t);
  assert(i < p->len);
  *child = p->prod[i].var;
  *exp = p->prod[i].exp;
}






/*
 * Value of constant terms
 * - t must be a constant term of appropriate type
 * - generic_const_value(table, t) works for any constant 
 *   term t of scalar or uninterpreted type
 */
bool bool_const_value(term_table_t *table, term_t t) {
  assert(t == true_term || t == false_term);
  return is_pos_term(t);
}

void arith_const_value(term_table_t *table, term_t t, mpq_t q) {
  assert(is_pos_term(t));
  q_get_mpq(rational_term_desc(table, t), q);
}

void arith_ff_const_value(term_table_t *table, term_t t, mpq_t q) {
  assert(is_pos_term(t));
  q_get_mpq(finitefield_term_desc(table, t), q);
}

void bv_const_value(term_table_t *table, term_t t, int32_t a[]) {
  bvconst64_term_t *bv64;
  bvconst_term_t *bv;

  switch (term_kind(table, t)) {
  case BV64_CONSTANT:
    bv64 = bvconst64_term_desc(table, t);
    bvconst64_get_array(bv64->value, a, bv64->bitsize);
    break;

  case BV_CONSTANT:
    bv = bvconst_term_desc(table, t);
    bvconst_get_array(bv->data, a, bv->bitsize);
    break;

  default:
    assert(false);
    break;
  }
}

// constant of uninterpreted or scalar type (not Boolean)
int32_t generic_const_value(term_table_t *table, term_t t) {
  assert(is_pos_term(t) && t != true_term);
  return constant_term_index(table, t);
}

