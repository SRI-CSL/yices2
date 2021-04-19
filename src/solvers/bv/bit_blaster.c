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
 * Conversion of bitvector constraints into clauses
 */

#include <assert.h>

#include "solvers/bv/bit_blaster.h"
#include "utils/int_array_sort.h"



#define TRACE 0

#if TRACE

#include <stdio.h>
#include "solvers/cdcl/smt_core_printer.h"

static void trace_cbuffer(cbuffer_t *buffer);

static void trace_unit_clause(bit_blaster_t *s, literal_t a);
static void trace_binary_clause(literal_t a, literal_t b);
static void trace_ternary_clause(literal_t a, literal_t b, literal_t c);
static void trace_quad_clause(literal_t a, literal_t b, literal_t c, literal_t d);

static void trace_clause(uint32_t n, literal_t *a);

#endif




/************************
 *  CLAUSE-SET BUFFER   *
 ***********************/

/*
 * Initialize buffer:
 * - nclauses = 0
 * - var[j] = null_bvar for all j
 */
static void init_cbuffer(cbuffer_t *buffer) {
  uint32_t j;

  buffer->def = null_bvar;
  for (j=0; j<CBUFFER_NVARS; j++) {
    buffer->var[j] = null_bvar;
  }
  buffer->is_unsat = false;
  buffer->nclauses = 0;
}


/*
 * Reset: clear all variables
 * - clear the unsat flag and reset nclauses to 0
 */
static inline void reset_cbuffer(cbuffer_t *buffer) {
  init_cbuffer(buffer);
}


/*
 * Activate and initialize a new clause of index buffer->nclauses
 * - this does not increase nclauses
 */
static uint32_t cbuffer_new_clause_idx(cbuffer_t *buffer) {
  uint32_t i, j;

  assert(buffer->nclauses < CBUFFER_NCLAUSES);
  i = buffer->nclauses;
  buffer->signature[i] = 0;

  for (j=0; j<CBUFFER_NVARS; j++) {
    buffer->data[i][j] = 0;
  }

  return i;
}


/*
 * Return the index of variable x in buffer
 * - if x is not present, add it and return its index
 */
static uint32_t cbuffer_var_idx(cbuffer_t *buffer, bvar_t x) {
  uint32_t j;

  assert(x >= 0);

  j = 0;
  for (;;) {
    assert(j < CBUFFER_NVARS);
    if (buffer->var[j] < 0) break;
    if (buffer->var[j] == x) return j;
    j ++;
  }

  buffer->var[j] = x;

  return j;
}



/*
 * Conversion from literal sign to a polarity code in cbuffer
 * - pos_lit(x): sign = 0 --> code = +1
 * - neg_lit(x): sign = 1 --> code = -1
 * so code = 1 - 2 * sign
 */
static inline int8_t literal_code(literal_t l) {
  int32_t sign;
  sign = sign_of_lit(l);
  return 1 - sign - sign;
}

/*
 * Code for not l = 2 * sign - 1 = - code for l
 */
static inline int8_t opposite_code(literal_t l) {
  int32_t sign;
  sign = sign_of_lit(l);
  return sign + sign - 1;
}


/*
 * Add literal l to clause i
 * - return true if that makes the clause true
 *   (i.e., if clause i contains not(l))
 * - return false otherwise
 */
static inline bool cbuffer_add_lit(cbuffer_t *buffer, uint32_t i, literal_t l) {
  uint32_t j;

  assert(0 <= i && i < CBUFFER_NCLAUSES);
  j = cbuffer_var_idx(buffer, var_of(l));
  if (buffer->data[i][j] == opposite_code(l)) {
    return true;
  }
  buffer->data[i][j] = literal_code(l);
  buffer->signature[i] |= (uint8_t)(1<<j);

  return false;
}


/*
 * Check whether clause i is empty (unsat)
 */
static bool cbuffer_empty_clause(cbuffer_t *buffer, uint32_t i) {
  uint32_t j;

  for (j=0; j<CBUFFER_NVARS; j++) {
    if (buffer->data[i][j] != 0) {
      return false;
    }
  }
  return true;
}


/*
 * Remove literal at index j of clause i
 */
static inline void cbuffer_remove_lit(cbuffer_t *buffer, uint32_t i, uint32_t j) {
  assert(0 <= i && i < CBUFFER_NCLAUSES && 0 <= j && j < CBUFFER_NVARS);
  buffer->data[i][j] = 0;
  buffer->signature[i] &= ~((uint8_t)(1<<j));
}



/*
 * Check whether clause i subsumes clause k
 * (i.e., all literals of clause i occur in clause k)
 */
static bool cbuffer_subsumes(cbuffer_t *buffer, uint32_t i, uint32_t k) {
  uint32_t j;

  assert(0 <= i && i < CBUFFER_NCLAUSES && 0 <= k && k < CBUFFER_NCLAUSES);
  for (j=0; j<CBUFFER_NVARS; j++) {
    // subsumption means c[i][j] = 0 or c[i][j] = c[k][j]
    if (buffer->data[i][j] != buffer->data[k][j] && buffer->data[i][j] != 0) {
      return false;
    }
  }
  return true;
}


/*
 * Resolution: check whether clauses i and k can be resolved.
 * - if they can, return the index j such that data[i][j] = - data[k][j]
 *   Clause i is of the form (A or l) and clause k is (B or not(l)),
 *   with l = pos_lit(var[j]) or neg_lit(var[j]).
 * - if they can't be resolved, return -1
 */
static int32_t cbuffer_resolver_index(cbuffer_t *buffer, uint32_t i, uint32_t k) {
  uint32_t j;
  int32_t f;

  f = -1;
  assert(0 <= i && i < CBUFFER_NCLAUSES && 0 <= k && k < CBUFFER_NCLAUSES);
  for (j=0; j<CBUFFER_NVARS; j++) {
    if (buffer->data[i][j] != 0 && buffer->data[k][j] != 0 &&
        buffer->data[i][j] != buffer->data[k][j]) {
      // clause i and clause k have opposite literals for var[j]
      if (f < 0) {
        f = j;
      } else {
        return -1;
      }
    }
  }
  return f;
}


/*
 * Check whether clause i is alive (not marked)
 */
static inline bool live_clause(cbuffer_t *buffer, uint32_t i) {
  assert(0 <= i && i < CBUFFER_NCLAUSES);
  return (buffer->mask & (((uint32_t) 1) << i)) == 0;
}

/*
 * Remove clause i from the set: set its mark bit
 */
static inline void kill_clause(cbuffer_t *buffer, uint32_t i) {
  assert(0 <= i && i < CBUFFER_NCLAUSES);
  buffer->mask |= (((uint32_t) 1) << i);
}


/*
 * Check whether all variables of clause i occur in clause k
 */
static inline bool var_subset(cbuffer_t *buffer, uint32_t i, uint32_t k) {
  assert(0 <= i && i < CBUFFER_NCLAUSES && 0 <= k && k < CBUFFER_NCLAUSES);
  return (uint8_t) ((~buffer->signature[i]) | buffer->signature[k]) == (uint8_t) 0xFF;
}


/*
 * Check whether clause i is subsumed by another clause
 * - if so, remove i from the clause set (set bit 1 of mask)
 */
static void remove_clause_if_subsumed(cbuffer_t *buffer, uint32_t i) {
  uint32_t k, n;

  assert(0 <= i && i < buffer->nclauses && live_clause(buffer, i));

  n = buffer->nclauses;
  for (k=0; k<n; k++) {
    if (k != i && live_clause(buffer, k) && var_subset(buffer, k, i) &&
        cbuffer_subsumes(buffer, k, i)) {
      kill_clause(buffer, i);
      break;
    }
  }
}


/*
 * Remove all clauses subsumed by clause i
 */
static void remove_clauses_subsumed(cbuffer_t *buffer, uint32_t i) {
  uint32_t k, n;

  assert(0 <= i && i < buffer->nclauses && live_clause(buffer, i));

  n = buffer->nclauses;
  for (k=0; k<n; k++) {
    if (k != i && live_clause(buffer, k) && var_subset(buffer, i, k) &&
        cbuffer_subsumes(buffer, i, k)) {
      kill_clause(buffer, k);
    }
  }
}


/*
 * Attempt resolution/subsumption
 * - search for two live clauses i and k such that
 *   clause[i] = (A or l) and clause[k] = (A or B or not(l))
 * - replace clause[k] by the resolvent (A or B)
 * - remove all clauses subsumed by (A or B)
 * Return true if such a pair was found
 */
static bool resolution_subsumption(cbuffer_t *buffer) {
  uint32_t i, k, n;
  int32_t j;

  n = buffer->nclauses;
  for (k=0; k<n; k++) {
    if (live_clause(buffer, k)) {
      for (i=0; i<n; i++) {
        if (i != k && live_clause(buffer, i) && var_subset(buffer, i, k)) {
          // var_of(clause[i]) is a subset of var_of(clause[k])
          j = cbuffer_resolver_index(buffer, i, k);
          if (j >= 0) {
            // replace clause[k] = (A or B or not(l)) by (A or B)
            cbuffer_remove_lit(buffer, k, j);
            remove_clauses_subsumed(buffer, k);
            return true;
          }
        }
      }
    }
  }

  return false;
}


/*
 * Remove all the dead clauses
 */
static void remove_dead_clauses(cbuffer_t *buffer) {
  uint32_t i, j, k, n;

  if (buffer->mask != 0) {
    n = buffer->nclauses;
    k = 0;
    for (i=0; i<n; i++) {
      if (live_clause(buffer, i)) {
        if (k < i) {
          // copy clause[i] into clause[k];
          for (j=0; j<CBUFFER_NVARS; j++) {
            buffer->data[k][j] = buffer->data[i][j];
          }
          buffer->signature[k] = buffer->signature[i];
        }
        k ++;
      }
    }
    buffer->mask = 0;
    buffer->nclauses = k;
  }
}



/*
 * Simplify the set of clauses
 */
static void cbuffer_simplify(cbuffer_t *buffer) {
  uint32_t i, n;

  n = buffer->nclauses;
  if (buffer->is_unsat || n <= 1) return;

  buffer->mask = 0;

  for (i=0; i<n; i++) {
    if (live_clause(buffer, i)) {
      remove_clause_if_subsumed(buffer, i);
    }
  }

  remove_dead_clauses(buffer);

  while (resolution_subsumption(buffer)) {
  }

  remove_dead_clauses(buffer);
}


/*
 * Convert var + code to a literal
 * - code must be non-zero
 * - if code = +1 return pos_lit(v)
 * - if code = -1 return neg_lit(v)
 */
static inline literal_t code2lit(bvar_t v, int8_t code) {
  assert(code != 0 && v >= 0);
  return code == 1 ? pos_lit(v) : neg_lit(v);
}


/*
 * Copy clause i into array a
 * - a must be large enough (i.e., CBUFFER_NVARS)
 * - return the number of literals in a
 */
static uint32_t cbuffer_extract_clause(cbuffer_t *buffer, uint32_t i, literal_t *a) {
  uint32_t j, n;
  int8_t code;

  n = 0;
  for (j=0; j<CBUFFER_NVARS; j++) {
    code = buffer->data[i][j];
    if (code != 0) {
      a[n] = code2lit(buffer->var[j], code);
      n ++;
    }
  }
  return n;
}


/*
 * Get the number of variables in buffer
 */
static uint32_t cbuffer_nvars(cbuffer_t *buffer) {
  uint32_t j, n;

  n = 0;
  for (j=0; j<CBUFFER_NVARS; j++) {
    n += (buffer->var[j] >= 0);
  }
  return n;
}


/*****************
 *  BIT BLASTER  *
 ****************/

/*
 * Initialization:
 * - solver and remap must be initialized outside this function
 */
void init_bit_blaster(bit_blaster_t *s, smt_core_t *solver, remap_table_t *remap) {
  s->solver = solver;
  s->remap = remap;
  s->htbl = get_gate_table(solver);
  init_cbuffer(&s->buffer);
  init_ivector(&s->aux_vector, 0);
  init_ivector(&s->aux_vector2, 0);
  init_ivector(&s->aux_vector3, 0);
  init_ivector(&s->aux_vector4, 0);
  s->last_fresh = null_bvar;
}


/*
 * Deletion: doesn't delete the solver
 */
void delete_bit_blaster(bit_blaster_t *s) {
  s->solver = NULL;
  s->htbl = NULL;
  delete_ivector(&s->aux_vector);
  delete_ivector(&s->aux_vector2);
  delete_ivector(&s->aux_vector3);
  delete_ivector(&s->aux_vector4);
}


/*
 * Reset buffers
 */
void reset_bit_blaster(bit_blaster_t *s) {
  reset_cbuffer(&s->buffer);
  ivector_reset(&s->aux_vector);
  ivector_reset(&s->aux_vector2);
  ivector_reset(&s->aux_vector3);
  ivector_reset(&s->aux_vector4);
  s->last_fresh = null_bvar;
}






/*********************
 *  INTERFACE LAYER  *
 ********************/

/*
 * Set of functions for communicating with the solver
 * by invoking the corresponding functions in the smt_core.
 */
static inline bval_t base_value(bit_blaster_t *s, literal_t l) {
  return literal_base_value(s->solver, l);
}

static inline void bit_blaster_add_empty_clause(bit_blaster_t *s) {
  add_empty_clause(s->solver);
}

static void bit_blaster_add_unit_clause(bit_blaster_t *s, literal_t l) {
#if TRACE
  trace_unit_clause(s, l);
#endif
  add_unit_clause(s->solver, l);
}

static void bit_blaster_add_binary_clause(bit_blaster_t *s, literal_t l1, literal_t l2) {
#if TRACE
  trace_binary_clause(l1, l2);
#endif
  add_binary_clause(s->solver, l1, l2);
}


#if 0
static void bit_blaster_add_ternary_clause(bit_blaster_t *s, literal_t l1, literal_t l2, literal_t l3) {
#if TRACE
  trace_ternary_clause(l1, l2, l3);
#endif
  add_ternary_clause(s->solver, l1, l2, l3);
}

static void bit_blaster_add_quad_clause(bit_blaster_t *s, literal_t l1, literal_t l2, literal_t l3, literal_t l4) {
  literal_t aux[4];

#if TRACE
  trace_quad_clause(l1, l2, l3, l4);
#endif

  aux[0] = l1;
  aux[1] = l2;
  aux[2] = l3;
  aux[3] = l4;

  add_clause(s->solver, 4, aux);
}
#endif

// clauses with an optional defined var x
static void bit_blaster_add_clause(bit_blaster_t *s, bvar_t x, uint32_t n, literal_t *a) {
#if TRACE
  trace_clause(n, a);
#endif
  if (x == null_bvar || x != s->last_fresh) {
    add_clause(s->solver, n, a);
  } else {
    add_def_clause(s->solver, x, n, a);
  }
}

static void bit_blaster_add_binary_def_clause(bit_blaster_t *s, bvar_t x, literal_t l1, literal_t l2) {
#if TRACE
  trace_binary_clause(l1, l2);
#endif
  if (x == null_bvar || x != s->last_fresh) {
    add_binary_clause(s->solver, l1, l2);
  } else {
    add_binary_def_clause(s->solver, x, l1, l2);
  }
}

static void bit_blaster_add_ternary_def_clause(bit_blaster_t *s, bvar_t x, literal_t l1, literal_t l2, literal_t l3) {
#if TRACE
  trace_ternary_clause(l1, l2, l3);
#endif
  if (x == null_bvar || x  != s->last_fresh) {
    add_ternary_clause(s->solver, l1, l2, l3);
  } else {
    add_ternary_def_clause(s->solver, x, l1, l2, l3);
  }
}

static void bit_blaster_add_quad_def_clause(bit_blaster_t *s, bvar_t x, literal_t l1, literal_t l2, literal_t l3, literal_t l4) {
  literal_t aux[4];

#if TRACE
  trace_quad_clause(l1, l2, l3, l4);
#endif

  aux[0] = l1;
  aux[1] = l2;
  aux[2] = l3;
  aux[3] = l4;

  if (x == null_bvar || x != s->last_fresh) {
    add_clause(s->solver, 4, aux);
  } else {
    add_def_clause(s->solver, x, 4, aux);
  }
}

bvar_t bit_blaster_new_var(bit_blaster_t *s) {
  bvar_t x;

  x = create_boolean_variable(s->solver);
  s->last_fresh = x;
  return x;
}



/*************************
 *  CLAUSE CONSTRUCTION  *
 ************************/

/*
 * Add literal l to clause i (at the end) unless it's true or false
 * - return true if the clause c becomes true (i.e., if l is true)
 */
static bool sclause_push(bit_blaster_t *s, cbuffer_t *buffer, uint32_t i, literal_t l) {
  switch (base_value(s, l)) {
  case VAL_FALSE: // skip l
    return false;
  case VAL_UNDEF_TRUE:
  case VAL_UNDEF_FALSE:
    return cbuffer_add_lit(buffer, i, l);
  case VAL_TRUE:
  default: // prevents GCC warning
    return true;
  }
}



/*
 * Add clause {a, b} to buffer
 */
static void push_binary_clause(bit_blaster_t *s, cbuffer_t *buffer, literal_t a, literal_t b) {
  bool true_clause;
  uint32_t i;

  if (buffer->is_unsat) return;

  i = cbuffer_new_clause_idx(buffer);
  true_clause = sclause_push(s, buffer, i, a) || sclause_push(s, buffer, i, b);
  if (! true_clause) {
    buffer->is_unsat = cbuffer_empty_clause(buffer, i);
    buffer->nclauses = i+1;
  }
}

/*
 * Add clause {a, b, c}
 */
static void push_ternary_clause(bit_blaster_t *s, cbuffer_t *buffer,
                                literal_t a, literal_t b, literal_t c) {
  bool true_clause;
  uint32_t i;

  if (buffer->is_unsat) return;

  i = cbuffer_new_clause_idx(buffer);
  true_clause = sclause_push(s, buffer, i, a) || sclause_push(s, buffer, i, b) ||
    sclause_push(s, buffer, i, c);
  if (! true_clause) {
    buffer->is_unsat = cbuffer_empty_clause(buffer, i);
    buffer->nclauses = i+1;
  }
}


/*
 * Add a clause {a, b, c, d}
 */
static void push_quad_clause(bit_blaster_t *s, cbuffer_t *buffer,
                             literal_t a, literal_t b, literal_t c, literal_t d) {
  bool true_clause;
  uint32_t i;

  if (buffer->is_unsat) return;

  i = cbuffer_new_clause_idx(buffer);
  true_clause = sclause_push(s, buffer, i, a) || sclause_push(s, buffer, i, b) ||
    sclause_push(s, buffer, i, c) || sclause_push(s, buffer, i, d);
  if (! true_clause) {
    buffer->is_unsat = cbuffer_empty_clause(buffer, i);
    buffer->nclauses = i+1;
  }
}




/*
 * Assert all the clauses in buffer then reset buffer
 * - if buffer->is_unsat holds, add the empty clause
 */
static void commit_buffer(bit_blaster_t *s, cbuffer_t *buffer) {
  literal_t aux[CBUFFER_NVARS];
  uint32_t i, n, k;
  bvar_t x;

#if TRACE
  trace_cbuffer(buffer);
#endif

  if (buffer->is_unsat) {
    bit_blaster_add_empty_clause(s);
  } else {
    n = buffer->nclauses;
    x = buffer->def;
    for (i=0; i<n; i++) {
      k = cbuffer_extract_clause(buffer, i, aux);
      bit_blaster_add_clause(s, x, k, aux);
    }
  }
  reset_cbuffer(buffer);
}





/*
 * LARGE OR
 */
#ifndef NDEBUG

/*
 * For debugging, check whether v is strictly increasing
 * and doesn't contain two literals with the same variable
 */
static bool normalized_vector(ivector_t *v) {
  uint32_t i, n;

  n = v->size;
  if (n > 1) {
    for (i=0; i<n-1; i++) {
      if (var_of(v->data[i]) >= var_of(v->data[i+1])) {
        return false;
      }
    }
  }
  return true;
}

#endif



/*
 * Simplify (OR a[0] ... a[n-1]): store the result in v
 * - remove false literals
 * - check for true literals and complementary literals
 * - remove duplicates
 */
static void simplify_or(bit_blaster_t *s, literal_t *a, uint32_t n, ivector_t *v) {
  uint32_t i, j;
  literal_t l, aux;

  ivector_reset(v);
  for (i=0; i<n; i++) {
    l = a[i];
    switch (base_value(s, l)) {
    case VAL_FALSE:
      break;
    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      ivector_push(v, l);
      break;
    case VAL_TRUE:
      goto or_is_true;
    }
  }


  /*
   * Sort, remove duplicates, and check for complementary literals
   */
  n = v->size;
  if (n > 1) {
    int_array_sort(v->data, n);
    l = v->data[0];
    j = 1;
    for (i=1; i<n; i++) {
      aux = v->data[i];
      if (aux != l) {
        if (aux == not(l)) goto or_is_true;
        v->data[j] = aux;
        l = aux;
        j ++;
      }
    }

    ivector_shrink(v, j);
  }
  return;

 or_is_true:
  ivector_reset(v);
  ivector_push(v, true_literal);
  return;
}

/*
 * Find a literal in v with the same boolean variable as x (i.e., equal to x or not(x))
 * - return the index k such that v->data[k] = x or v->data[k] = not(x)
 * - return -1 if x does not occur in v
 */
static int32_t find_in_vector(ivector_t *v, literal_t x) {
  literal_t *a;
  uint32_t l, h, k;
  bvar_t vx;

  assert(normalized_vector(v) && v->size > 0);

  vx = var_of(x);

  // binary search for a literal with same variable as x
  l = 0;
  h = v->size;
  a = v->data;
  for (;;) {
    k = (l + h) >> 1;  // no overflow possible here (cf. MAX_VECTOR_SIZE)
    assert(l <= k && k < h && h <= v->size);
    if (k == l) break;
    if (var_of(a[k]) > vx) {
      h = k;
    } else {
      l = k;
    }
  }

  if (var_of(a[k]) == vx) {
    return k;
  } else {
    return -1;
  }
}


/*
 * Assert clauses for the constraint x = (OR a[0] ... a[n-1])
 * - the literals a[0] ... a[n-1] are stored in vector v
 * - v must be normalized and non-empty
 * - v may be  modified
 *
 * Add clauses: { x, ~a[0]}
 *                 ...
 *              { x, ~a[n-1]}
 *          { ~x, a[0], ..., a[n-1] }
 *
 * Special cases:
 *   x is true or false
 *   x is a[i] or ~a[i]
 */
static void assert_ordef_clauses(bit_blaster_t *s, literal_t x, ivector_t *v) {
  uint32_t i, n;
  int32_t k;
  literal_t aux, *a;

  assert(v->size > 0);

  n = v->size;
  a = v->data;

  switch (base_value(s, x)) {
  case VAL_FALSE:
    for (i=0; i<n; i++) {
      bit_blaster_add_unit_clause(s, not(a[i]));
    }
    break;

  case VAL_UNDEF_FALSE:
  case VAL_UNDEF_TRUE:
    k = find_in_vector(v, x);
    if (k < 0) {
      // No simplifications
      for (i=0; i<n; i++) {
        bit_blaster_add_binary_def_clause(s, var_of(x), x, not(a[i]));
      }
      ivector_push(v, not(x));
      bit_blaster_add_clause(s, var_of(x), n+1, v->data);

    } else {
      assert(0 <= k && k < n);

      aux = a[k];
      if (x == aux) {
        /*
         * Constraint x == (or a[0] ... x ... a[n-1])
         * Need clauses { x, ~a[0] } ... { x, ~a[n-1] }
         */
        for (i=0; i<n; i++) {
          if (i != k) {
            assert(a[i] != x && a[i] != not(x));
            bit_blaster_add_binary_clause(s, x, not(a[i]));
          }
        }
      } else {
        /*
         * Constraint x == (or a[0] ... ~x ... a[n-1])
         * Clauses: { x } and { a[0], ..., a[n-1] }
         */
        assert(aux == not(x));
        bit_blaster_add_unit_clause(s, x);

        // remove ~x from v (may be overkill?)
        for (i=k+1; i<n; i++) {
          assert(a[i] != x && a[i] != not(x));
          a[i-1] = a[i];
        }
        bit_blaster_add_clause(s, null_bvar, n-1, a);

      }
    }
    break;

  case VAL_TRUE:
    bit_blaster_add_clause(s, null_bvar, n, a);
    break;
  }
}




/*
 * LARGE XOR
 */

/*
 * Simplify (xor (xor a[0] ... a[n-1]) x)
 * - the result is given by vector v and the returned integer
 * - the returned value is either 0 or 1
 * - if it's 0 the result is (XOR v[0] ... v[p-1])
 * - if it's 1 the result is not (XOR v[0] ... v[p-1])
 *
 * To build (xor a[0] ... a[n-1]) use x = false_literal.
 *
 * HACK: the simplifications use bit-tricks that are dependent
 * on the literal representation, namely,
 * low-order bit = 0 for positive literals
 * low-order bit = 1 for negative literals
 */
static uint32_t simplify_xor(bit_blaster_t *s, uint32_t n, literal_t *a, literal_t x, ivector_t *v) {
  uint32_t i, sgn, j;
  literal_t l;

  ivector_reset(v);
  sgn = 0;


  /*
   * remove true/false literals and negative literals
   */
  for (i=0; i<n; i++) {
    l = a[i];
    switch (base_value(s, l)) {
    case VAL_FALSE:
      break;
    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      sgn ^= sign_of_lit(l);  // flip sgn if l is negative
      l &= ~1;                // remove sign of l = low-order bit
      ivector_push(v, l);
      break;
    case VAL_TRUE:
      sgn ^= 1;
      break;
    }
  }

  // add x if needed
  switch (base_value(s, x)) {
  case VAL_FALSE:
    break;
  case VAL_UNDEF_FALSE:
  case VAL_UNDEF_TRUE:
    sgn ^= sign_of_lit(x);  // flip sign is x is negative
    x &= ~1;                 // remove sign of x
    ivector_push(v, x);
    break;
  case VAL_TRUE:
    sgn ^= 1;
    break;
  }


  n = v->size;

  // sort then remove duplicates
  if (n > 1) {
    a = v->data;

    int_array_sort(a, n);
    j = 0;
    i = 0;
    while (i<n-1) {
      l = a[i];
      if (l == a[i+1]) { // (xor l l) --> 0
        i += 2;
      } else {
        a[j] = l;
        j ++;
        i ++;
      }
    }
    if (i == n-1){
      a[j] = a[i];
      j ++;
    }

    ivector_shrink(v, j);
  }

  return sgn;
}



/*
 * Assert (xor a b) and (xor a b c)
 * These xor encode a defintion x = (xor ...) so x is the variable defined by
 * thesse xor constraints.
 */
static void bit_blaster_assert_xor3(bit_blaster_t *s, bvar_t x, literal_t a, literal_t b, literal_t c) {
  bit_blaster_add_ternary_def_clause(s, x, a, b, c);
  bit_blaster_add_ternary_def_clause(s, x, a, not(b), not(c));
  bit_blaster_add_ternary_def_clause(s, x, not(a), b, not(c));
  bit_blaster_add_ternary_def_clause(s, x, not(a), not(b), c);
}


/*
 * Assert (xor a b c d)
 */
// clauses for (xor a b c d) = 1
static void bit_blaster_assert_xor4(bit_blaster_t *s, bvar_t x, literal_t a, literal_t b, literal_t c, literal_t d) {
  bit_blaster_add_quad_def_clause(s, x, a, b, c, d);
  bit_blaster_add_quad_def_clause(s, x, a, b, not(c), not(d));
  bit_blaster_add_quad_def_clause(s, x, a, not(b), c, not(d));
  bit_blaster_add_quad_def_clause(s, x, a, not(b), not(c), d);
  bit_blaster_add_quad_def_clause(s, x, not(a), b, c, not(d));
  bit_blaster_add_quad_def_clause(s, x, not(a), b, not(c), d);
  bit_blaster_add_quad_def_clause(s, x, not(a), not(b), c, d);
  bit_blaster_add_quad_def_clause(s, x, not(a), not(b), not(c), not(d));
}



/*
 * Create a fresh literal l and assert l = (xor a b))
 * (i.e., (xor a b not(l)) = 1)
 */
static inline literal_t make_xor2(bit_blaster_t *s, literal_t a, literal_t b) {
  literal_t l;

  l = bit_blaster_fresh_literal(s);
  bit_blaster_assert_xor3(s, var_of(l), a, b, not(l));
  return l;
}


/*
 * Same thing for (xor a b c)
 */
static inline literal_t make_xor3(bit_blaster_t *s, literal_t a, literal_t b, literal_t c) {
  literal_t l;

  l = bit_blaster_fresh_literal(s);
  bit_blaster_assert_xor4(s, var_of(l), a, b, c, not(l));
  return l;
}


/*
 * Create a new literal l then add the clauses l = (xor a[0] ... a[n-1])
 * - n must be at least 2
 */
static literal_t bit_blaster_create_xor(bit_blaster_t *s, uint32_t n, literal_t *a) {
  literal_t l;
  uint32_t i;

  assert(n >= 2);

  l = a[0];
  for (i=1; i<n-1; i += 2) {
    l = make_xor3(s, l, a[i], a[i+1]);
  }
  if (i < n) {
    assert(i == n-1);
    l = make_xor2(s, l, a[i]);
  }

  return l;
}





/**********************************
 *  ENCODING OF ELEMENTARY GATES  *
 *********************************/

/*
 * Constraint: (a = b) or (xor a b) = 0
 */
void bit_blaster_eq(bit_blaster_t *s, literal_t a, literal_t b) {
  cbuffer_t *buffer;

  buffer = &s->buffer;
  assert(buffer->nclauses == 0);

  push_binary_clause(s, buffer, a, not(b));
  push_binary_clause(s, buffer, not(a), b);

  if (cbuffer_nvars(buffer) != 2) {
    cbuffer_simplify(buffer);
  }

  //  printf("BB: assert eq %"PRId32" %"PRId32"\n", a, b);

  commit_buffer(s, buffer);
}


/*
 * Constraint: x = (xor a b) or (xor a b x) = 0
 */
static void bit_blaster_xor2_gate(bit_blaster_t *s, literal_t a, literal_t b, literal_t x) {
  cbuffer_t *buffer;

  buffer = &s->buffer;
  assert(buffer->nclauses == 0);

  buffer->def = var_of(x);
  push_ternary_clause(s, buffer, not(a), not(b), not(x));
  push_ternary_clause(s, buffer, not(a), b, x);
  push_ternary_clause(s, buffer, a, not(b), x);
  push_ternary_clause(s, buffer, a, b, not(x));

  if (cbuffer_nvars(buffer) != 3) {
    cbuffer_simplify(buffer);
  }
  commit_buffer(s, buffer);
}


/*
 * Constraint: x = (xor a b c) or (xor a b c x) = 0
 */
static void bit_blaster_xor3_gate(bit_blaster_t *s, literal_t a, literal_t b, literal_t c, literal_t x) {
  cbuffer_t *buffer;

  buffer = &s->buffer;
  assert(buffer->nclauses == 0);

  buffer->def = var_of(x);
  push_quad_clause(s, buffer, not(a), not(b), not(c), x);
  push_quad_clause(s, buffer, not(a), not(b), c, not(x));
  push_quad_clause(s, buffer, not(a), b, not(c), not(x));
  push_quad_clause(s, buffer, a, not(b), not(c), not(x));
  push_quad_clause(s, buffer, a, b, c, not(x));
  push_quad_clause(s, buffer, a, b, not(c), x);
  push_quad_clause(s, buffer, a, not(b), c, x);
  push_quad_clause(s, buffer, not(a), b, c, x);

  if (cbuffer_nvars(buffer) != 4) {
    cbuffer_simplify(buffer);
  }
  commit_buffer(s, buffer);
}


/*
 * Constraint: x = (or a b)
 */
static void bit_blaster_or2_gate(bit_blaster_t *s, literal_t a, literal_t b, literal_t x) {
  cbuffer_t *buffer;

  buffer = &s->buffer;
  assert(buffer->nclauses == 0);

  buffer->def = var_of(x);
  push_binary_clause(s, buffer, not(a), x);
  push_binary_clause(s, buffer, not(b), x);
  push_ternary_clause(s, buffer, a, b, not(x));

  if (cbuffer_nvars(buffer) != 3) {
    cbuffer_simplify(buffer);
  }
  commit_buffer(s, buffer);
}




/*
 * Constraint: x = (ite c a b)
 */
static void bit_blaster_mux(bit_blaster_t *s, literal_t c, literal_t a, literal_t b, literal_t x) {
  cbuffer_t *buffer;

  buffer = &s->buffer;
  assert(buffer->nclauses == 0);

  buffer->def = var_of(x);
  push_ternary_clause(s, buffer, c, b, not(x));
  push_ternary_clause(s, buffer, c, not(b), x);
  push_ternary_clause(s, buffer, not(c), a, not(x));
  push_ternary_clause(s, buffer, not(c), not(a), x);

#if 1
  // optional: two more clauses (improve BCP in SAT solver)
  push_ternary_clause(s, buffer, a, b, not(x));
  push_ternary_clause(s, buffer, not(a), not(b), x);
#endif

  if (cbuffer_nvars(buffer) != 4) {
    cbuffer_simplify(buffer);
  }
  commit_buffer(s, buffer);
}


/*
 * Constraint: x = (majority a b c)
 */
static void bit_blaster_maj3(bit_blaster_t *s, literal_t a, literal_t b, literal_t c, literal_t x) {
  cbuffer_t *buffer;

  buffer = &s->buffer;
  assert(buffer->nclauses == 0);

  buffer->def = var_of(x);
  push_ternary_clause(s, buffer, a, b, not(x));
  push_ternary_clause(s, buffer, not(a), not(b), x);
  push_ternary_clause(s, buffer, a, c, not(x));
  push_ternary_clause(s, buffer, not(a), not(c), x);
  push_ternary_clause(s, buffer, b, c, not(x));
  push_ternary_clause(s, buffer, not(b), not(c), x);

  if (cbuffer_nvars(buffer) != 4) {
    cbuffer_simplify(buffer);
  }
  commit_buffer(s, buffer);
}


/*
 * Constraint: x = (cmp a b c)
 * Defined as: x = ((a > b) or (a = b and c))
 *
 * This is used to encode (bvuge u v) or (bvsge u v) via the following equations:
 * 1) (bvuge u v) = (u[n] > v[n]) or (u[n] == v[n] and (bvuge u[n-1 .. 1] v[n-1 .. 1]))
 * 2) (bvsge u v) = (v[n] > u[n]) or (u[n] == v[n] and (bvuge u[n-1 .. 1] v[n-1 .. 1]))
 */
static void bit_blaster_cmp(bit_blaster_t *s, literal_t a, literal_t b, literal_t c, literal_t x) {
  // use equivalence (cmp a b c) = (majority a (not b) c)
  bit_blaster_maj3(s, a, not(b), c, x);
}



/*
 * Constraint x = (or a[0] ... a[n-1])
 */
static void bit_blaster_or_gate(bit_blaster_t *s, uint32_t n, literal_t *a, literal_t x) {
  ivector_t *v;

  v = &s->aux_vector;
  simplify_or(s, a, n, v);
  n = v->size;
  if (n == 0) {
    // x = false
    if (base_value(s, x) != VAL_FALSE) {
#if TRACE
      trace_unit_clause(s, not(x));
#endif
      bit_blaster_add_unit_clause(s, not(x));
    }
  } else if (n == 1 && v->data[0] == true_literal) {
    // x = true
    if (base_value(s, x) != VAL_TRUE) {
#if TRACE
      trace_unit_clause(s, x);
#endif
      bit_blaster_add_unit_clause(s, x);
    }
  } else {
    // general case
    assert_ordef_clauses(s, x, v);
  }
}


/*
 * BIT ADDERS
 */

/*
 * NOTE: it would probably be better to add the clauses for x and y to
 * cbuffer then simplify, rather than simplify the clauses for x then
 * the clauses for y.
 */

/*
 * Half adder: x = sum a+b, y = carry
 */
static void bit_blaster_half_adder(bit_blaster_t *s, literal_t a, literal_t b, literal_t x, literal_t y) {
  bit_blaster_xor2_gate(s, a, b, x);               // x = a + b
  bit_blaster_or2_gate(s, not(a), not(b), not(y)); // y = a and b
}

/*
 * Full adder: x = (a + b + c) mod 2, y = carry
 */
static void bit_blaster_full_adder(bit_blaster_t *s, literal_t a, literal_t b, literal_t c, literal_t x, literal_t y) {
  bit_blaster_xor3_gate(s, a, b, c, x);
  bit_blaster_maj3(s, a, b, c, y);
}



#if 0

// NOT USED
/*
 * Assert (or a b): apply simplifications
 */
static void bit_blaster_assert_or2(bit_blaster_t *s, literal_t a, literal_t b) {
  cbuffer_t *buffer;

  buffer = &s->buffer;
  assert(buffer->nclauses == 0);
  push_binary_clause(s, buffer, a, b);
  commit_buffer(s, buffer);
}

#endif



/*******************************
 *  EVALUATION/SIMPLIFICATION  *
 ******************************/

/*
 * Return true_literal or false_literal if l is true/false in solver
 * otherwise, return l
 */
static literal_t eval_literal(bit_blaster_t *s, literal_t l) {
  switch (base_value(s, l)) {
  case VAL_FALSE:
    return false_literal;
  case VAL_TRUE:
    return true_literal;
  case VAL_UNDEF_FALSE:
  case VAL_UNDEF_TRUE:
  default:
    return l;
  }
}

/*
 * (xor a b)
 */
static literal_t bit_blaster_eval_xor2(bit_blaster_t *s, literal_t a, literal_t b) {
  a = eval_literal(s, a);
  b = eval_literal(s, b);

  if (a == b)             return false_literal;
  if (a == not(b))        return true_literal;
  if (a == true_literal)  return not(b);
  if (a == false_literal) return b;
  if (b == true_literal)  return not(a);
  if (b == false_literal) return a;

  return null_literal;
}

/*
 * (xor a b c)
 */
static literal_t bit_blaster_eval_xor3(bit_blaster_t *s, literal_t a, literal_t b, literal_t c) {
  a = eval_literal(s, a);
  b = eval_literal(s, b);
  c = eval_literal(s, c);

  if (a == b) return c;
  if (a == c) return b;
  if (b == c) return a;
  if (a == not(b)) return not(c);
  if (a == not(c)) return not(b);
  if (b == not(c)) return not(a);

  /*
   * No other simplifications are possible here
   * - a, b, and c are distinct and not complementary
   * So at least 2 of them are non constant
   */
  return null_literal;
}

/*
 * (or a b)
 */
static literal_t bit_blaster_eval_or2(bit_blaster_t *s, literal_t a, literal_t b) {
  a = eval_literal(s, a);
  b = eval_literal(s, b);

  if (a == b)             return a;
  if (a == not(b))        return true_literal;
  if (a == true_literal)  return true_literal;
  if (a == false_literal) return b;
  if (b == true_literal)  return true_literal;
  if (b == false_literal) return a;

  return null_literal;
}

/*
 * (and a b): return null_literal if that does not simplify
 */
static literal_t bit_blaster_eval_and2(bit_blaster_t *s, literal_t a, literal_t b) {
  literal_t l;

  l = bit_blaster_eval_or2(s, not(a), not(b));
  if (l != null_literal) {
    l = not(l);
  }
  return l;
}

/*
 * (ite c a b)
 */
static literal_t bit_blaster_eval_mux(bit_blaster_t *s, literal_t c, literal_t a, literal_t b) {
  c = eval_literal(s, c);
  a = eval_literal(s, a);
  b = eval_literal(s, b);

  /*
   * (ite true  a b) --> a
   * (ite false a b) --> b
   */
  if (c == true_literal)  return a;
  if (c == false_literal) return b;

  /*
   * (ite c  c b) --> (ite c true  b)
   * (ite c ~c b) --> (ite c false b)
   */
  if (a == c) {
    a = true_literal;
  } else if (a == not(c)) {
    a = false_literal;
  }

  /*
   * (ite c a  c) = (ite c a false)
   * (ite c a ~c) = (ite c a  true)
   */
  if (b == c) {
    b = false_literal;
  } else if (b == not(c)) {
    b = true_literal;
  }

  /*
   * (ite c a a) --> a
   * (ite c true false) --> c
   * (ite c false true) --> not c
   */
  if (a == b) return a;
  if (a == true_literal && b == false_literal) return c;
  if (a == false_literal && b == true_literal) return not(c);

  return null_literal;
}


/*
 * (a > b): i.e. (a and not b)
 */
static literal_t bit_blaster_eval_gt(bit_blaster_t *s, literal_t a, literal_t b) {
  a = eval_literal(s, a);
  b = eval_literal(s, b);

  if (a == b)             return false_literal;
  if (a == not(b))        return a;
  if (a == true_literal)  return not(b);
  if (a == false_literal) return false_literal;
  if (b == true_literal)  return false_literal;
  if (b == false_literal) return a;

  return null_literal;
}



/*
 * (majority a b c)
 */
static literal_t bit_blaster_eval_maj3(bit_blaster_t *s, literal_t a, literal_t b, literal_t c) {
  a = eval_literal(s, a);
  b = eval_literal(s, b);
  c = eval_literal(s, c);

  if (a == b)      return a;
  if (a == not(b)) return c;
  if (a == c)      return a;
  if (a == not(c)) return b;
  if (b == c)      return b;
  if (b == not(c)) return a;

  return null_literal;
}


/*
 * (cmp a b c) i.e., ((a > b) or (a = b and c))
 */
static literal_t bit_blaster_eval_cmp(bit_blaster_t *s, literal_t a, literal_t b, literal_t c) {
  // (cmp a b c) = (majority a (not b) c)
  return bit_blaster_eval_maj3(s, a, not(b), c);
}


/*
 * Simplify (bveq a b) where a and b are vectors on n bits
 */
literal_t bit_blaster_eval_bveq(bit_blaster_t *s, uint32_t n, literal_t *a, literal_t *b) {
  literal_t aux, la, lb;
  uint32_t i;

  aux = true_literal;

  for (i=0; i<n; i++) {
    la = eval_literal(s, a[i]);
    lb = eval_literal(s, b[i]);
    if (la == not(lb)) {
      aux = false_literal; // a[i] != b[i] so a != b
      break;
    } else if (la != lb) {
      aux = null_literal;   // can't tell yet
    }
  }

  return aux;
}




/************************
 *  GATE CONSTRUCTION   *
 ***********************/

/*
 * Create a new literal l then add the clauses for l = (or a[0] ... a[n-1])
 * This is similar to assert_ordef with the simplifications skipped.
 */
static literal_t bit_blaster_create_or(bit_blaster_t *s, ivector_t *v) {
  literal_t *a;
  literal_t l;
  uint32_t i, n;

  assert(v->size > 1);

  n = v->size;
  a = v->data;

  l = bit_blaster_fresh_literal(s);
  for (i=0; i<n; i++) {
    bit_blaster_add_binary_def_clause(s, var_of(l), l, not(a[i]));
  }

  ivector_push(v, not(l));
  bit_blaster_add_clause(s, var_of(l), n+1, v->data);

  return l;
}


/*
 * (or a[0] ... a[n-1])
 */
static literal_t bit_blaster_make_or(bit_blaster_t *s, uint32_t n, literal_t *a) {
  ivector_t *v;
  boolgate_t *g;
  literal_t l;

  v = &s->aux_vector;
  simplify_or(s, a, n, v);

  n = v->size;
  if (n == 0) return false_literal;
  if (n == 1) return v->data[0];

  if (n <= BIT_BLASTER_MAX_HASHCONS_SIZE) {
    g = gate_table_get_or(s->htbl, n, v->data);
    l = g->lit[n];  // output literal for an or gate
    if (l == null_literal) {
      // this is a new gate
      l = bit_blaster_create_or(s, v);
      g->lit[n] = l;
    }
  } else {
    // No hash consing
    l = bit_blaster_create_or(s, v);
  }

  return l;
}


/*
 * (or a b)
 */
static literal_t bit_blaster_make_or2(bit_blaster_t *s, literal_t a, literal_t b) {
  literal_t aux[2];

  aux[0] = a;
  aux[1] = b;
  return bit_blaster_make_or(s, 2, aux);
}


/*
 * (xor a[0] ... a[n-1])
 */
static literal_t bit_blaster_make_xor(bit_blaster_t *s, uint32_t n, literal_t *a) {
  ivector_t *v;
  boolgate_t *g;
  uint32_t sgn;
  literal_t l;

  v = &s->aux_vector;
  sgn = simplify_xor(s, n, a, false_literal, v);

  n = v->size;
  if (n == 0) return false_literal ^ sgn;  // i.e., sgn = 1 --> true_literal
  if (n == 1) return v->data[0] ^ sgn;     // i.e., sgn = 1 --> not v[0]

  if (n <= BIT_BLASTER_MAX_HASHCONS_SIZE) {
    /*
     * Check the hash table
     */
    g = gate_table_get_xor(s->htbl, n, v->data);
    l = g->lit[n]; // output literal for XOR gate
    if (l == null_literal) {
      // new XOR gate
      l = bit_blaster_create_xor(s, n, v->data);
      g->lit[n] = l;
    }
  } else {
    // no hash consing
    l = bit_blaster_create_xor(s, n, v->data);
  }

  return l ^ sgn;
}



/*
 * (xor a b)
 */
literal_t bit_blaster_make_xor2(bit_blaster_t *s, literal_t a, literal_t b) {
  literal_t aux[2];

  aux[0] = a;
  aux[1] = b;
  return bit_blaster_make_xor(s, 2, aux);
}



/*
 * Assert l = (xor a b) and add an xor gate to the hash table.
 * - the gate must not be in the table already
 */
static void make_xor2_gate(bit_blaster_t *s, literal_t a, literal_t b, literal_t l) {
  boolgate_t *g;
  literal_t aux;

  // normalize
  if (a > b) {
    aux = a; a = b; b = aux;
  }
  g = gate_table_get_xor2(s->htbl, a, b);
  assert(g->lit[2] == null_literal);
  g->lit[2] = l;
  bit_blaster_xor2_gate(s, a, b, l);
}


/*
 * Search for l == (or a b) if such an l already exists
 * - create a fresh l and add a gate to the hash-table if the gate does not exist
 * - this is similar but more efficient than bit_blaster_make_or2
 */
static literal_t make_or2(bit_blaster_t *s, literal_t a, literal_t b) {
  boolgate_t *g;
  literal_t aux;

  /*
   * try to simplify first
   */
  aux = bit_blaster_eval_or2(s, a, b);
  if (aux == null_literal) {
    /*
     * look in the hash table for (xor a b)
     * - normalize first: arguments must be in increasing order
     */
    if (a > b) {
      aux = a; a = b; b = aux;
    }
    g = gate_table_get_or2(s->htbl, a, b);
    aux = g->lit[2];
    if (aux == null_literal) {
      aux = bit_blaster_fresh_literal(s);
      g->lit[2] = aux;
      bit_blaster_or2_gate(s, a, b, aux);
    }
  }

  return aux;
}

/*
 * Return a literal l = (and a b)
 * This gets turned into not(l) = (or not(a) not(b)).
 * - if l does not exist, create a fresh literal and gate, and add the clauses
 *   for (not l) == (or not(a) not(b)).
 */
static inline literal_t make_and2(bit_blaster_t *s, literal_t a, literal_t b) {
  return not(make_or2(s, not(a), not(b)));
}




/*
 * Build l = (cmp a b c)
 *
 * NOTE: we could add more normalization
 * since (cmp a b c) = (cmp (not b) (not a) c).
 */
static literal_t make_cmp(bit_blaster_t *s, literal_t a, literal_t b, literal_t c) {
  boolgate_t *g;
  literal_t l;

  /*
   * Try simplification, then hash-consing
   */
  l = bit_blaster_eval_cmp(s, a, b, c);
  if (l == null_literal) {
    g = gate_table_get_cmp(s->htbl, a, b, c);
    l = g->lit[3]; // output
    if (l == null_literal) {
      // create a fresh l and assert l = (cmp a b c)
      l = bit_blaster_fresh_literal(s);
      bit_blaster_cmp(s, a, b, c, l);
      g->lit[3] = l;
    }
  }
  assert(l != null_literal);
  return l;
}


/*
 * Create (ite c a b) with output x and add it to the hash table.
 * Also add the clauses for (x == (ite c a b))
 * The gate must not exist already.
 */
static void make_mux_aux(bit_blaster_t *s, literal_t c, literal_t a, literal_t b, literal_t x) {
  boolgate_t *g;

  assert(gate_table_find_ite(s->htbl, c, a, b) == NULL);

  g = gate_table_get_ite(s->htbl, c, a, b);
  assert(g->lit[3] == null_literal);
  g->lit[3] = x; // store x as output of (ite c a b)
  bit_blaster_mux(s, c, a, b, x);
}


/*
 * Normalize then build (ite c a b) with output x.
 */
static void make_mux(bit_blaster_t *s, literal_t c, literal_t a, literal_t b, literal_t x) {
  literal_t l;

  /*
   * Normalization: ensure all (ite u y z) gates in the hash table
   * have u and y positive.
   *
   * x == (ite (not c) a b) <--> x == (ite c b a)
   * x == (ite c (not a) b) <--> (not x) == (ite c a (not b))
   */
  if (is_neg(c)) {
    l = a; a = b; b = l; // swap a and b
    c = not(c);
  }
  if (is_neg(a)) {
    make_mux_aux(s, c, not(a), not(b), not(x));
  } else {
    make_mux_aux(s, c, a, b, x);
  }
}


/*
 * Assert (s, c) = half-add(a, b) and add the gate to the hash table.
 * The gate must not be present in the table.
 */
static void make_half_add(bit_blaster_t *s, literal_t a, literal_t b, literal_t sum, literal_t c) {
  boolgate_t *g;
  literal_t aux;

  // normalize: ensure a <= b
  if (a > b) {
    aux = a; a = b; b = aux;
  }

  assert(gate_table_find_halfadd(s->htbl, a, b) == NULL);
  g = gate_table_get_halfadd(s->htbl, a, b);
  assert(g->lit[2] == null_literal && g->lit[3] == null_literal);
  g->lit[2] = sum;
  g->lit[3] = c;
  bit_blaster_half_adder(s, a, b, sum, c);
}


/*
 * Store a, b, c in increasing order in array v[3]
 */
static void sort3(literal_t a, literal_t b, literal_t c, literal_t *v) {
  if (a <= b) {
    if (a <= c) {
      v[0] = a;
      if (b <= c) {
        v[1] = b; v[2] = c;
      } else {
        v[1] = c; v[2] = b;
      }
    } else {
      v[0] = c; v[1] = a; v[2] = b;
    }
  } else { // b < a
    if (b <= c) {
      v[0] = b;
      if (a <= c) {
        v[1] = a; v[2] = c;
      } else {
        v[1] = c; v[2] = a;
      }
    } else {
      v[0] = c; v[1] = b; v[2] = a;
    }
  }
  assert(v[0] <= v[1] && v[1] <= v[2]);
}



/*
 * Assert (sum, d) = full-add(a, b, c) and add the gate to the hash table.
 * The gate must not be present in the hash table.
 * - sum is the sum and d is the carry
 */
static void make_full_add(bit_blaster_t *s, literal_t a, literal_t b, literal_t c,
                          literal_t sum, literal_t d) {
  boolgate_t *g;
  literal_t aux[3];

  // normalize
  sort3(a, b, c, aux);
  assert(gate_table_find(s->htbl, fulladdgate_tag(), aux) == NULL);
  g = gate_table_get(s->htbl, fulladdgate_tag(), aux);
  assert(g->lit[3] == null_literal && g->lit[4] == null_literal);
  g->lit[3] = sum;
  g->lit[4] = d;
  bit_blaster_full_adder(s, a, b, c, sum, d);
}





/*********************
 *  FIND OPERATIONS  *
 ********************/

/*
 * The following functions check whether a specific gate simplifies
 * or is present in the gate table.
 */

/*
 * Search for l == (xor a b) if such an l already exists
 * return null_literal it there's no such l.
 */
static literal_t find_xor2(bit_blaster_t *s, literal_t a, literal_t b) {
  boolgate_t *g;
  literal_t aux;

  /*
   * try to simplify first
   */
  aux = bit_blaster_eval_xor2(s, a, b);
  if (aux == null_literal) {
    /*
     * look in the hash table for (xor a b)
     * - normalize first: arguments must be in increasing order
     */
    if (a > b) {
      aux = a; a = b; b = aux;
    }
    aux = null_literal;
    g = gate_table_find_xor2(s->htbl, a, b);
    if (g != NULL) {
      aux = g->lit[2]; // output of binary gate
      assert(aux != null_literal);
    }
  }

  return aux;
}

/*
 * Search for l = (ite c a b) if such an l exists already.
 * Return null_literal if l does not exists.
 */
static literal_t find_mux(bit_blaster_t *s, literal_t c, literal_t a, literal_t b) {
  boolgate_t *g;
  literal_t l;

  l = bit_blaster_eval_mux(s, c, a, b);
  if (l == null_literal) {
    // search in the hash-table.

    /*
     * Normalization: all gates (ite x y ..) have x and y positive
     *
     * (ite (not c) a b) --> (ite c b a)
     * (ite c (not a) b) --> (not (ite c a (not b))
     */
    if (is_neg(c)) {
      l = a; a = b; b = l; // swap a and b
      c = not(c);
    }

    l = null_literal;
    if (is_neg(a)) {
      g = gate_table_find_ite(s->htbl, c, not(a), not(b));
      if (g != NULL) {
        assert(g->lit[3] != null_literal);
        l = not(g->lit[3]);
      }
    } else {
      g = gate_table_find_ite(s->htbl, c, a, b);
      if (g != NULL) {
        assert(g->lit[3] != null_literal);
        l = g->lit[3];
      }
    }
  }
  return l;
}


/*
 * Search for (s, c) = half_add(a, b): s = sum, c = carry
 * Set s and c to null if the gate is not found
 */
static void find_half_add(bit_blaster_t *s, literal_t a, literal_t b, literal_t *sum, literal_t *c) {
  boolgate_t *g;
  literal_t s0, c0;

  /*
   * eval_xor(a, b) and eval_or(a, b) should either be
   * both null or both non-null.
   */
  s0 = bit_blaster_eval_xor2(s, a, b);  // s0 = a + b
  if (s0 != null_literal) {
    c0 = bit_blaster_eval_and2(s, a, b); // c0 = (and a b)
    assert(c0 != null_literal);
    *sum = s0;
    *c = c0;
  } else {
    assert(bit_blaster_eval_and2(s, a, b) == null_literal);
    // normalize: ensure a <= b
    if (a > b) {
      c0 = a; a = b; b = c0;
    }
    g = gate_table_find_halfadd(s->htbl, a, b);
    if (g != NULL) {
      assert(g->lit[2] != null_literal && g->lit[3] != null_literal);
      *sum = g->lit[2];
      *c = g->lit[3];
    } else {
      *sum = null_literal;
      *c = null_literal;
    }
  }
}


/*
 * Search for (sum, d) = full-add(a, b, c): d = carry
 * Set s and d to null if the gate is not found
 */
static void find_full_add(bit_blaster_t *s, literal_t a, literal_t b, literal_t c,
                          literal_t *sum, literal_t *d) {
  boolgate_t *g;
  literal_t aux[3];
  literal_t s0, d0;

  /*
   * eval_xor(a, b, c) and eval_maj3(a, b, c) should either be
   * both null or both non-null.
   */
  s0 = bit_blaster_eval_xor3(s, a, b, c);  // s0 = a + b + c
  if (s0 != null_literal) {
    d0 = bit_blaster_eval_maj3(s, a, b, c); // carry
    assert(d0 != null_literal);
    *sum = s0;
    *d = d0;
  } else {
    assert(bit_blaster_eval_maj3(s, a, b, c) == null_literal);
    // normalize: ensure a <= b <= c
    sort3(a, b, c, aux);
    g = gate_table_find(s->htbl, fulladdgate_tag(), aux);
    if (g != NULL) {
      assert(g->lit[3] != null_literal && g->lit[4] != null_literal);
      *sum = g->lit[3];
      *d = g->lit[4];
    } else {
      *sum = null_literal;
      *d = null_literal;
    }
  }
}





/*************************
 *  COMPARATOR CIRCUITS  *
 ************************/

/*
 * EQUALITY
 */

/*
 * Equality: return l such that the equivalence l == (bveq a b)
 * holds in the solver.
 * - a and b must be literal arrays of size n
 * - n should be positive but the function will give the right
 *   answer (i.e., true_literal) if n == 0.
 * - all elements in a and b must be non-null literals
 *
 * l is (not (or (xor a[0] b[0]) ... (xor a[n-1] b[n-1])))
 */
literal_t bit_blaster_make_bveq(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  uint32_t i;

  v = &s->aux_vector2;
  resize_ivector(v, n);
  ivector_reset(v);
  aux = v->data;

  /*
   * We want aux[i] = (xor a[i] b[i]) for i=0 to n-1
   * The first pass does not create any new gate or literal, but it
   * may leave aux[i] undefined (i.e., null_literal).
   * The second pass builds aux[i] := (xor a[i] b[i]) for real.
   */
  for (i=0; i<n; i++) {
    aux[i] = find_xor2(s, a[i], b[i]);
    if (aux[i] == true_literal) return false_literal; // a[i] != b[i] so a != b
  }
  for (i=0; i<n; i++) {
    if (aux[i] == null_literal) {
      // TODO?: use a simpler/faster constructor
      // rather than the generic make_xor2
      aux[i] = bit_blaster_make_xor2(s, a[i], b[i]);
    }
  }

  return not(bit_blaster_make_or(s, n, aux));
}




/*
 * ARITHMETIC COMPARATORS
 */

/*
 * Check whether (cmp a b c) is independent of c
 * If so return l = (cmp a b ?).
 *
 * Since (cmp a b c) = (a>b) or (a = b and c), we check
 * whether (a != b) holds then return l = (a>b).
 */
static literal_t find_cmp_cut(bit_blaster_t *s, literal_t a, literal_t b) {
  a = eval_literal(s, a);
  b = eval_literal(s, b);

  if (a == not(b)) return a;
  return null_literal;
}


/*
 * Unsigned comparison: return l such that the equivalence l == (a >= b) holds
 * in the solver.
 * - a and b must be literal arrays of size n
 * - n = 0 is allowed: the function will give the right answer (true_literal).
 * - all elements in a and b must be non-null literals
 *
 * l is (bcmp a[n-1] b[n-1] (bcmp a[n-2] b[n-2] ... (bcmp a[0] b[0] true) .. ))
 * If (bcmp a[i] b[i] (bcmp ..)) = c, independent of a[i-1], b[i-1],..,a[0], b[0],
 * we build (bcmp a[n-1] b[n-1] (bcmp a[n-2] b[n-2] ... (bcmp a[i+1] b[i+1] c) ..))
 */
literal_t bit_blaster_make_bvuge(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  literal_t c;
  uint32_t i;

  /*
   * Check a[i-1] > b[i-1], starting with i = n
   * stop when (bcmp a[i-1] b[i-1] ..) does not depend on bits
   *  i-2 ... 0
   */
  i = n;
  for (;;) {
    if (i == 0) {
      c = true_literal;
      break;
    }
    c = find_cmp_cut(s, a[i-1], b[i-1]);
    if (c != null_literal) break;
    i --;
  }

  /*
   * Build (cmp a[n-1] b[n-1] (cmp a[n-2] b[n-2] .. (cmp a[i] b[i] c) ..))
   */
  assert(c != null_literal && 0 <= i && i <= n);
  while (i < n) {
    c = make_cmp(s, a[i], b[i], c);
    i ++;
  }

  return c;
}



/*
 * Signed comparison: return l such that the equivalence l == (a >= b) holds
 * in the solver, with a and b interpreted as signed integers.
 * - a and b must be literal arrays of size n
 * - n must be positive
 * - all elements in a and b must be non-null literals
 *
 * l is (bcmp b[n-1] a[n-1] c)
 * where c = (bvuge a[n-1:0] b[n-1:0])
 */
literal_t bit_blaster_make_bvsge(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  literal_t c;

  assert(n > 0);

  /*
   * Check the sign bits: if (cmp b[n-1] a[n-1] c)
   * does not depend on c, stop.
   * Otherwise the result is (cmp b[n-1] a[n-1] c)
   * where c = (bvuge a[n-1:0] b[n-1:0])
   */
  c = find_cmp_cut(s, b[n-1], a[n-1]);
  if (c != null_literal) {
    return c;
  } else {
    c = bit_blaster_make_bvuge(s, a, b, n-1);
    return make_cmp(s, b[n-1], a[n-1], c);
  }
}




/*
 * EQUALITY/INEQUALITY ASSERTIONS
 */

/*
 * Assert a == b
 */
void bit_blaster_assert_bveq(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    bit_blaster_eq(s, a[i], b[i]);
  }
}


/*
 * Assert a != b: (or (xor a[0] b[0] ... a[n-1] b[n-1]))
 * If n=0, this leads to UNSAT.
 */
void bit_blaster_assert_bvneq(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  uint32_t i;

  v = &s->aux_vector2;
  resize_ivector(v, n);
  ivector_reset(v);
  aux = v->data;

  /*
   * We want aux[i] = (xor a[i] b[i]) for i=0 to n-1
   * The first pass does not create any new gate or literal, but it
   * may leave aux[i] undefined (i.e., null_literal).
   * The second pass builds aux[i] := (xor a[i] b[i]) for real.
   */
  for (i=0; i<n; i++) {
    aux[i] = find_xor2(s, a[i], b[i]);
    if (aux[i] == true_literal) {
      // a[i] != b[i] so a != b
      return;
    }
  }
  for (i=0; i<n; i++) {
    if (aux[i] == null_literal) {
      // TODO?: use a simpler/faster constructor
      // rather than the generic make_xor2
      aux[i] = bit_blaster_make_xor2(s, a[i], b[i]);
    }
  }

  bit_blaster_or_gate(s, n, aux, true_literal);
}


/*
 * Assert a >= b, unsigned.
 */
void bit_blaster_assert_bvuge(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;
  literal_t l;

  /*
   * Reduction in this loop:
   * (bvuge a[i ... 0] b[i ... 0]) is equivalent to
   *   (a[i] = b[i) and (bvuge a[i-1 ... 0] b[i-2 ... 0])
   * if (a[i] > b[i]) is false
   */
  i = n;
  for (;;) {
    if (i == 0) return; // nothing to assert
    i --;
    if (bit_blaster_eval_gt(s, a[i], b[i]) != false_literal) break;
    bit_blaster_eq(s, a[i], b[i]);
  }

  assert(0 <= i && i < n);

  /*
   * Now assert (a[i] > b[i]) or ((a[i] = b[i]) and (bvuge a[i-1 ... 0] b[i-1 ... 0]))
   */
  l = find_cmp_cut(s, a[i], b[i]);
  if (l != null_literal) {
    // (a[i] = b[i]) is false and l is equivalent to (a[i] > b[i])
    bit_blaster_add_unit_clause(s, l);
  } else {
    // no simplification
    l = bit_blaster_make_bvuge(s, a, b, i); // l is (bvuge a[i-1 ... 0] b[i-1 ... 0])
    bit_blaster_cmp(s, a[i], b[i], l, true_literal); // assert (cmp a[i] b[i] l) == true
  }
}


/*
 * Assert a < b, unsigned.
 */
void bit_blaster_assert_bvult(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;
  literal_t l;

  /*
   * (bvlt a[i...0] b[i...0]) is
   * (a[i] < b[i]) or (a[i] = b[i] and (bvlt a[i-1...0] b[i-1...0]))
   * This is equivalent to (a[i] = b[i]) and (bvlt a[i-1...0] b[i-1...0])
   * if (b[i] > a[i]) is false
   */
  i = n;
  for (;;) {
    if (i == 0) {
      // we've asserted a[0] = b[0] ... a[n-1] = b[n-1] so (a < b) is unsat
      bit_blaster_add_empty_clause(s);
      return;
    }
    i --;
    if (bit_blaster_eval_gt(s, b[i], a[i]) != false_literal) break;
    bit_blaster_eq(s, a[i], b[i]);
  }

  assert(0 <= i && i < n);

  /*
   * Assert (not (bvuge a[i...0] b[i...0]))
   */
  l = find_cmp_cut(s, b[i], a[i]);
  if (l != null_literal) {
    // (a[i] = b[i]) is false and l is equivalent to (b[i] > a[i])
    bit_blaster_add_unit_clause(s, l);
  } else {
    // no simplification
    l = bit_blaster_make_bvuge(s, a, b, i); // l is (bvuge a[i-1...0] b[i-1...0])
    bit_blaster_cmp(s, a[i], b[i], l, false_literal); // assert (cmp a[i] b[i] l) == false
  }
}


/*
 * Assert a >= b, unsigned. n must be positive.
 */
void bit_blaster_assert_bvsge(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  literal_t l;

  assert(n > 0);

  n --;
  /*
   * (a[n...0] >= b[n...0]) is (b[n] > a[n]) or (a[n] = b[n] and (bvuge a[n-1...0] b[n-1...0]))
   * that's (b[n] = a[n]) and (bvuge a[n-1...0] b[n-1...0]) if (b[n] > a[n]) is false
   */
  if (bit_blaster_eval_gt(s, b[n], a[n]) == false_literal) {
    bit_blaster_eq(s, a[n], b[n]);
    bit_blaster_assert_bvuge(s, a, b, n); // (bvuge a[n-1...0] b[n-1...0])
  } else {
    l = find_cmp_cut(s, b[n], a[n]);
    if (l != null_literal) {
      // b[n] == a[n] is false, l is equivalent to (b[n] > a[n])
      bit_blaster_add_unit_clause(s, l);
    } else {
      // no simplification
      l = bit_blaster_make_bvuge(s, a, b, n);
      bit_blaster_cmp(s, b[n], a[n], l, true_literal);
    }
  }
}


/*
 * Assert a < b, unsigned. n must be positive.
 */
void bit_blaster_assert_bvslt(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  literal_t l;

  assert(n > 0);

  n --;
  /*
   * (bvslt a[n...0] b[n...0]) is
   * (a[n] > b[n]) or (a[n] = b[n] and not (bvuge a[n-1...0] b[n-1...0]))
   * That's equivalent to
   * (a[n] = b[n]) and (bvult a[n-1...0] b[n-1...0]) if (a[n] > b[n]) is false
   */
  if (bit_blaster_eval_gt(s, a[n], b[n]) == false_literal) {
    bit_blaster_eq(s, a[n], b[n]);
    bit_blaster_assert_bvult(s, a, b, n);
  } else {
    l = find_cmp_cut(s, a[n], b[n]);
    if (l != null_literal) {
      // a[n] = b[n] is false, l is equivalent to (a[n] > b[n])
      bit_blaster_add_unit_clause(s, l);
    } else {
      // no simplification
      l = bit_blaster_make_bvuge(s, a, b, n);
      bit_blaster_cmp(s, a[n], b[n], not(l), true_literal);
    }
  }
}




/*
 * Constraints of the form l == (comparison a b)
 */

/*
 * Assert l = (bveq a b)
 */
void bit_blaster_make_bveq2(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t l, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  uint32_t i;

  switch (base_value(s, l)) {
  case VAL_FALSE:
    bit_blaster_assert_bvneq(s, a, b, n);
    break;

  case VAL_TRUE:
    bit_blaster_assert_bveq(s, a, b, n);
    break;

  default:
    v = &s->aux_vector2;
    resize_ivector(v, n);
    ivector_reset(v);
    aux = v->data;

    /*
     * We want aux[i] = (xor a[i] b[i]) for i=0 to n-1
     * The first pass does not create any new gate or literal, but it
     * may leave aux[i] undefined (i.e., null_literal).
     * The second pass builds aux[i] := (xor a[i] b[i]) for real.
     */
    for (i=0; i<n; i++) {
      aux[i] = find_xor2(s, a[i], b[i]);
      if (aux[i] == true_literal) {
        // l must be false since a[i] != b[i]
        bit_blaster_add_unit_clause(s, not(l));
        return;
      }
    }
    for (i=0; i<n; i++) {
      if (aux[i] == null_literal) {
        // TODO?: use a simpler/faster constructor
        // rather than the generic make_xor2
        aux[i] = bit_blaster_make_xor2(s, a[i], b[i]);
      }
    }

    // assert not(l) == (or (xor a[0] b[0]) ... (xor a[n-1] b[n-1]))
    bit_blaster_or_gate(s, n, aux, not(l));
    break;
  }
}



/*
 * Assert l = (a >= b) unsigned
 */
void bit_blaster_make_bvuge2(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t l, uint32_t n) {
  literal_t l0;

  switch (base_value(s, l)) {
  case VAL_FALSE:
    bit_blaster_assert_bvult(s, a, b, n);
    break;

  case VAL_TRUE:
    bit_blaster_assert_bvuge(s, a, b, n);
    break;

  default:
    l0 = bit_blaster_make_bvuge(s, a, b, n);
    bit_blaster_eq(s, l0, l);
    break;
  }
}


/*
 * Assert l = (a >= b) signed
 */
void bit_blaster_make_bvsge2(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t l, uint32_t n) {
  literal_t c;

  assert(n > 0);

  switch (base_value(s, l)) {
  case VAL_FALSE:
    bit_blaster_assert_bvslt(s, a, b, n);
    break;

  case VAL_TRUE:
    bit_blaster_assert_bvsge(s, a, b, n);
    break;

  default:
    c = find_cmp_cut(s, b[n-1], a[n-1]);
    if (c != null_literal) {
      bit_blaster_eq(s, c, l);
    } else {
      c = bit_blaster_make_bvuge(s, a, b, n-1);
      bit_blaster_cmp(s, b[n-1], a[n-1], c, l);
    }
    break;
  }
}



/**************************************
 *  CONSTRAINTS WITH PSEUDO-LITERALS  *
 *************************************/

/*
 * Get the literal mapped to pseudo-literal u
 * - create a fresh literal and attach it to u if needed
 */
static literal_t concretize_pseudo_lit(bit_blaster_t *s, literal_t u) {
  remap_table_t *rmap;
  literal_t f;

  rmap = s->remap;
  f = remap_table_find(rmap, u);
  if (f == null_literal) {
    f = bit_blaster_fresh_literal(s);
    remap_table_assign(rmap, u, f);
  }

  return f;
}

/*
 * Equality: u == l
 * - u is a pseudo literal
 * - l is a literal
 */
static void assert_pseudo_eq(bit_blaster_t *s, literal_t u, literal_t l) {
  remap_table_t *rmap;
  literal_t f;

  assert(l != null_literal);

  rmap = s->remap;
  f = remap_table_find(rmap, u);
  if (f == null_literal) {
    remap_table_assign(rmap, u, l);
  } else {
    bit_blaster_eq(s, f, l);
  }
}


/*
 * Assert u = (ite c a b)
 * - u must be a pseudo literal
 * - c, a, and b must be literals
 */
static void assert_pseudo_mux(bit_blaster_t *s, literal_t c, literal_t a, literal_t b, literal_t u) {
  literal_t f, l;

  l = find_mux(s, c, a, b);
  if (l == null_literal) {
    f = concretize_pseudo_lit(s, u);
    make_mux(s, c, a, b, f);
  } else {
    assert_pseudo_eq(s, u, l);
  }
}


/*
 * Assert (a == u) where a is an array of n literals
 * and u is an array of n pseudo literals.
 */
static void assert_pseudo_bveq(bit_blaster_t *s, literal_t *u, literal_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    assert_pseudo_eq(s, u[i], a[i]);
  }
}



/*****************
 *  MULTIPLEXER  *
 ****************/

/*
 * Assert u = (ite c a b).
 * - circuit input: two literals arrays a and b of size n
 *                + control literal c
 * - circuit output: pseudo-literal array u of size n
 */
void bit_blaster_make_bvmux(bit_blaster_t *s, literal_t c, literal_t *a, literal_t *b,
                            literal_t *u, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    assert_pseudo_mux(s, c, a[i], b[i], u[i]); // u[i] == (ite c a[i] b[i])
  }
}



/**********************
 *  BASIC ARITHMETIC  *
 *********************/

/*
 * NEGATION
 */

/*
 * Assert u = (bvneg a)
 * - input a: array of n literals
 * - output u: array of n pseudo literals
 */
void bit_blaster_make_bvneg(bit_blaster_t *s, literal_t *a, literal_t *u, uint32_t n) {
  uint32_t i;
  literal_t sum, f, c, d;

  /*
   * we use (bvneg a) = (bvnot a) + 1
   * The sum (bvnot a) + 1 is constructed using half adders
   */
  c = true_literal;
  for (i=0; i<n; i++) {
    find_half_add(s, not(a[i]), c, &sum, &d);
    if (sum == null_literal) {
      assert(d == null_literal);
      /*
       * create half_add(not(a[i]), c)
       * u[i] := sum, d := carry out
       */
      f = concretize_pseudo_lit(s, u[i]);
      d = bit_blaster_fresh_literal(s);
      make_half_add(s, not(a[i]), c, f, d);
    } else {
      assert(d != null_literal);
      /*
       * Assert sum = u[i]
       */
      assert_pseudo_eq(s, u[i], sum);
    }
    c = d;
  }
}


/*
 * ADDERS
 */

/*
 * Assert u = (bvadd a b)
 * - input: a and b must be arrays of n literals
 * - output u: array of n pseudo literals
 */
void bit_blaster_make_bvadd(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  uint32_t i;
  literal_t sum, f, c, d;

  c = false_literal; // carry in = 0

  for (i=0; i<n; i++) {
    find_full_add(s, a[i], b[i], c, &sum, &d);
    if (sum == null_literal) {
      assert(d == null_literal);
      /*
       * create full_add(a[i], b[i], c)
       * with u[i] := sum, d := carry out
       */
      f = concretize_pseudo_lit(s, u[i]);
      d = bit_blaster_fresh_literal(s);
      make_full_add(s, a[i], b[i], c, f, d);
    } else {
      assert(d != null_literal);
      /*
       * Assert sum = u[i]
       */
      assert_pseudo_eq(s, u[i], sum);
    }
    c = d;
  }
}

/*
 * Assert u = (bvsub a b)
 * - input: a and b must be arrays of n literals
 * - output u: array of n pseudo literals
 */
void bit_blaster_make_bvsub(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  uint32_t i;
  literal_t sum, f, c, d;

  // we do u = a + (bvnot b) + 1
  c = true_literal; // carry in = 1
  for (i=0; i<n; i++) {
    find_full_add(s, a[i], not(b[i]), c, &sum, &d);
    if (sum == null_literal) {
      assert(d == null_literal);
      /*
       * create full_add(a[i], b[i], c)
       * with u[i] := sum, d := carry out
       */
      f = concretize_pseudo_lit(s, u[i]);
      d = bit_blaster_fresh_literal(s);
      make_full_add(s, a[i], not(b[i]), c, f, d);
    } else {
      assert(d != null_literal);
      /*
       * Assert sum = u[i]
       */
      assert_pseudo_eq(s, u[i], sum);
    }
    c = d;
  }
}


/*
 * INCREMENT
 */

/*
 * Assert u = (bvadd a 2^k)
 * - input: a must be an array of n literals
 *          k must be an integer between 0 and n-1
 * - output u: array of n pseudo literals
 */
void bit_blaster_make_bvinc(bit_blaster_t *s, literal_t *a, uint32_t k, literal_t *u, uint32_t n) {
  literal_t sum, f, c, d;
  uint32_t i;

  assert(k < n);


  // bits[0 .. k-1] are not changed
  for (i=0; i<k; i++) {
    // u[i] := a[i]
    assert_pseudo_eq(s, u[i], a[i]);
  }

  // for bit[k .. b-1]: we use half adders
  // c = carry in
  c = true_literal;
  while (i<n) {
    find_half_add(s, a[i], c, &sum, &d);
    if (sum == null_literal) {
      assert(d == null_literal);
      /*
       * Create half_add(a[i], c)
       * u[i] := sum, d := carry out
       */
      f = concretize_pseudo_lit(s, u[i]);
      d = bit_blaster_fresh_literal(s);
      make_half_add(s, a[i], c, f, d);
    } else {
      assert(d != null_literal);
      /*
       * Assert sum = u[i]
       */
      assert_pseudo_eq(s, u[i], sum);
    }
    c = d;
    i ++;
  }
}

/*
 * DECREMENT
 */

/*
 * Carry of (a - b) = (not(a) and b)
 */
static inline literal_t decr_carry(bit_blaster_t *s, literal_t a, literal_t b) {
  return make_and2(s, not(a), b);
}


/*
 * Assert u = (bvsub a 2^k)
 * - input: a must be an array of n literals
 *          k must be an integer between 0 and n-1
 * - output u: array of n pseudo literals
 */
void bit_blaster_make_bvdec(bit_blaster_t *s, literal_t *a, uint32_t k, literal_t *u, uint32_t n) {
  literal_t diff, f, c;
  uint32_t i;

  assert(k < n);

  // bits[0 .. k-1] are not changed
  for (i=0; i<k; i++) {
    // u[i] := a[i]
    assert_pseudo_eq(s, u[i], a[i]);
  }

  // c = carry in
  c = true_literal;
  while (i<n) {
    // build diff = a[i] xor c
    diff = find_xor2(s, a[i], c);
    if (diff == null_literal) {
      f = concretize_pseudo_lit(s, u[i]);
      make_xor2_gate(s, a[i], c, f);
    } else {
      // assert u[i] = diff
      assert_pseudo_eq(s, u[i], diff);
    }

    // carry out
    c = decr_carry(s, a[i], c);
    i ++;
  }
}




/*
 * MULTIPLIER
 */

/*
 * Add (b * a * 2^k) to sum and assert (d = bit[k] of sum)
 * - a and sum must be arrays of n literals
 * - b must be a non-null literal
 * - d must be a non-null pseudo literal
 * - k must satisfy (0 <= k && k < n)
 */
static void bit_blaster_partial_product(bit_blaster_t *s, literal_t *sum, literal_t *a, uint32_t n,
                                        literal_t b, literal_t d, uint32_t k) {
  uint32_t i;
  literal_t p, f, s0, c0, d0;

  assert(0 <= k && k < n && b != null_literal);

  /*
   * If b == 0, sum doesn't change
   */
  if (b == false_literal) {
    // assert d == sum[k]
    assert_pseudo_eq(s, d, sum[k]);
    return;
  }

  /*
   * bit sum[k] needs special treatment
   */
  c0 = false_literal; // carry in
  p = make_and2(s, a[0], b);  // p = a[0] * b
  find_full_add(s, sum[k], p, c0, &s0, &d0); // s0 = sum[k] + p, d0 = carry out
  if (s0 == null_literal) {
    /*
     * fulladd (sum[k], p, c0) does not exist
     * create a new gate with output (f, d0)
     */
    assert(d0 == null_literal);
    d0 = bit_blaster_fresh_literal(s);
    f = concretize_pseudo_lit(s, d);
    make_full_add(s, sum[k], p, c0, f, d0);
    sum[k] = f;
  } else {
    /*
     * Found an existing pair (s0, d0) such that
     * fulladd (sum[k], p, c0) is (s0, d0).
     * Enforce d == s0.
     */
    assert_pseudo_eq(s, d, s0);
    sum[k] = s0;
  }
  c0 = d0;


  for (i=k+1; i<n; i++) {
    /*
     * Compute sum[i] := sum[i] + (a[i-k] * b) + c0
     * c0 = carry in
     * d0 = carry out
     */
    p = make_and2(s, a[i-k], b);  // p = a[i-k] * b
    find_full_add(s, sum[i], p, c0, &s0, &d0); // s0 = sum[i] + p + c0, d0 = carry out
    if (s0 == null_literal) {
      assert(d0 == null_literal);
      // create (fulladd s[i] p c0)
      s0 = bit_blaster_fresh_literal(s);
      d0 = bit_blaster_fresh_literal(s);
      make_full_add(s, sum[i], p, c0, s0, d0);
    }
    sum[i] = s0;
    c0 = d0;
  }
}


/*
 * Assert u = (bvmul a b)
 * - a and b must be arrays of n literals
 * - u must be an array of n non-null pseudo literals
 */
void bit_blaster_make_bvmul(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  uint32_t i;

  v = &s->aux_vector2;
  resize_ivector(v, n);
  ivector_reset(v);
  aux = v->data;

  /*
   * aux stores the sum a * b_i * 2^i for i=0 to n-1
   */
  for (i=0; i<n; i++) {
    aux[i] = false_literal;
  }

  /*
   * Compute aux := aux + a * b_i * 2^i
   * and assert u[i] = aux[i]
   */
  for (i=0; i<n; i++) {
    bit_blaster_partial_product(s, aux, a, n, b[i], u[i], i);
  }

}



/***************
 *  DIVISION   *
 **************/

/*
 * UNSIGNED DIVISION
 */

/*
 * Copy a[0...n-1] into aux[0...2n-1] with zero extension
 */
static void bit_blaster_zero_extend(literal_t *aux, literal_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    aux[i] = a[i];
  }
  for(i=n; i<2*n; i++) {
    aux[i] = false_literal;
  }
}

/*
 * Subtract (q * b) from a
 * - a and b must be arrays of n literals
 * - q must be a non-null literal
 */
static void bit_blaster_submul(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t q, uint32_t n) {
  uint32_t i;
  literal_t p, s0, c0, d0;

  if (q == false_literal) {
    return;
  }

  // a += a + (bvnot b*q) + 1
  c0 = true_literal; // carry in
  for (i=0; i<n; i++) {
    p = make_and2(s, b[i], q); // p = b[i] * q;
    find_full_add(s, a[i], not(p), c0, &s0, &d0); // s0 = a[i] + not(p) + c0, d0 = carry out
    if (s0 == null_literal) {
      assert(d0 == null_literal);
      // create (fulladd sum[k+i] p c0)
      s0 = bit_blaster_fresh_literal(s);
      d0 = bit_blaster_fresh_literal(s);
      make_full_add(s, a[i], not(p), c0, s0, d0);
    }
    a[i] = s0;
    c0 = d0;
  }
}


/*
 * Unsigned division:
 * - a and b must be literal arrays of size n
 * - q = either NULL or an array of n pseudo literals
 * - r = either NULL of an array of n pseudo literals
 *
 * Assert q = (bvudiv a b) and r = (bvurem a b)
 */
void bit_blaster_make_udivision(bit_blaster_t *s, literal_t *a, literal_t *b,
                                literal_t *q, literal_t *r, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  literal_t l;
  uint32_t i;

  v = &s->aux_vector2;
  resize_ivector(v, 2 * n);
  ivector_reset(v);
  aux = v->data;

  bit_blaster_zero_extend(aux, a, n); // aux := zero extend a to 2n bits
  i = n;
  while (i > 0) {
    i --;
    /*
     * bit i of quotient is 1 if (aux[i,..,i+n] >= b)
     */
    l = bit_blaster_make_bvuge(s, aux+i, b, n);
    bit_blaster_submul(s, aux+i, b, l, n);
    if (q != NULL) {
      // assert l = q[i]
      assert_pseudo_eq(s, q[i], l);
    }
  }

  // the remainder is in aux[n-1...0].
  // assert r == aux[n-1...0]
  if (r != NULL) {
    for (i=0; i<n; i++) {
      assert_pseudo_eq(s, r[i], aux[i]);
    }
  }
}


/*
 * SIGNED DIVISION
 */

/*
 * Store (bvneg a) into b
 */
static void bvneg_litarray(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;
  literal_t sum, c, d;

  c = true_literal;
  for (i=0; i<n; i++) {
    find_half_add(s, not(a[i]), c, &sum, &d); // sum = not(a[i]) + c, d = carry
    if (sum == null_literal) {
      assert(d == null_literal);
      sum = bit_blaster_fresh_literal(s);
      d = bit_blaster_fresh_literal(s);
      make_half_add(s, not(a[i]), c, sum, d);
    }
    b[i] = sum;
    c = d;
  }
}

/*
 * Store (bvmux c a b) into d
 */
static void bvmux_litarray(bit_blaster_t *s, literal_t c, literal_t *a, literal_t *b, literal_t *d, uint32_t n) {
  uint32_t i;
  literal_t l;

  for (i=0; i<n; i++) {
    l = find_mux(s, c, a[i], b[i]);
    if (l == null_literal) {
      l = bit_blaster_fresh_literal(s);
      make_mux(s, c, a[i], b[i], l);
    }
    d[i] = l;
  }
}

/*
 * Copy a into b
 */
static void bvcopy_litarray(literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    b[i] = a[i];
  }
}

/*
 * Store (absolute value of a) into b
 */
static void bvabs_litarray(bit_blaster_t *s, literal_t *a, literal_t *b, uint32_t n) {
  literal_t sa;

  assert(n > 0);
  sa = a[n-1]; // sign bit of a
  if (sa == false_literal) {
    bvcopy_litarray(a, b, n);
  } else {
    bvneg_litarray(s, a, b, n); // b := -a
    bvmux_litarray(s, sa, b, a, b, n); // b := (ite sa -a a)
  }
}


/*
 * Zero-extend a to size 2*n: set a[n ... 2n-1] to false
 * - a must be an array of 2n literals
 */
static void zero_extend_litarray(literal_t *a, uint32_t n) {
  uint32_t i;

  a += n;
  for (i=0; i<n; i++) {
    a[i] = false_literal;
  }
}


/*
 * Assert u == (if c then a else (bv-neg a))
 * - u is an array of n pseudo literals
 * - a is an array of n literals
 * - c is a non-null literal
 */
static void abseq_constraint(bit_blaster_t *s, literal_t c, literal_t *a, literal_t *u, uint32_t n) {
  literal_t *b;

  if (c == true_literal) {
    assert_pseudo_bveq(s, u, a, n);
  } else {
    b = (literal_t *) safe_malloc(n * sizeof(literal_t));
    bvneg_litarray(s, a, b, n);   // b := neg a
    bvmux_litarray(s, c, a, b, b, n); // b := if c then a else (neg a)
    assert_pseudo_bveq(s, u, b, n);
    safe_free(b);
  }
}



/*
 * Signed division
 * - a and b must be literal arrays of size n
 * - q = either NULL or an array of n pseudo literals
 * - r = either NULL of an array of n pseudo literals
 *
 * Assert q = (bvsdiv a b) and r = (bvsrem a b)
 */
void bit_blaster_make_sdivision(bit_blaster_t *s, literal_t *a, literal_t *b,
                                literal_t *q, literal_t *r, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  literal_t *abs_b;
  literal_t *quotient;
  literal_t l, sa, sb, same_sign;
  uint32_t i;

  assert(n > 0);

  v = &s->aux_vector2;
  resize_ivector(v, 2 * n);
  ivector_reset(v);
  aux = v->data;
  bvabs_litarray(s, a, aux, n); // aux = absolute value of a
  zero_extend_litarray(aux, n);

  v = &s->aux_vector3;
  resize_ivector(v, n);
  ivector_reset(v);
  abs_b = v->data;
  bvabs_litarray(s, b, abs_b, n); // abs_b = absolute value of b

  v = &s->aux_vector4;
  resize_ivector(v, n);
  ivector_reset(v);
  quotient = v->data;

  sa = a[n-1]; // sign bit of a
  sb = b[n-1]; // sign bit of b
  same_sign = bit_blaster_make_eq(s, sa, sb);

  /*
   * division: absolute value of a divided by absolute value of b
   */
  i = n;
  while (i > 0) {
    i --;
    l = bit_blaster_make_bvuge(s, aux+i, abs_b, n);
    bit_blaster_submul(s, aux+i, abs_b, l, n);
    quotient[i] = l;
  }

  /*
   * quotient[n-1 ... 0] = (udiv (abs a) (abs b))
   * aux[n-1 ... 0] = (urem (abs a) (abs b))
   */

  // q = (if same_sign then quotient else (bvneg quotient))
  if (q != NULL) {
    abseq_constraint(s, same_sign, quotient, q, n);
  }

  // r = (if (a >= 0) then aux[n-1 ..0] else (bvneg aux[n-1 ... 0])
  if (r != NULL) {
    abseq_constraint(s, not(sa), aux, r, n);
  }
}



/*
 * FLOOR DIVISION
 */

/*
 * Store (bvadd a b) into c
 * - a and b must be arrays of n literals
 * - c must be an empty array of size n
 */
static void bvadd_litarray(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *c, uint32_t n) {
  literal_t carry, sum, d;
  uint32_t i;

  carry = false_literal;
  for (i=0; i<n; i++) {
    find_full_add(s, a[i], b[i], carry, &sum, &d); // full adder: sum = a[i] + b[i] + carry, d = carry out
    if (sum == null_literal) {
      /*
       * the sum does no simplify and the adder does not
       * exist yet, create it
       */
      assert(d == null_literal);
      sum = bit_blaster_fresh_literal(s);
      d = bit_blaster_fresh_literal(s);
      make_full_add(s, a[i], b[i], carry, sum, d);
    }
    c[i] = sum;
    carry = d;
  }
}

/*
 * Remainder in the floor division of a by b:
 * - a and b must be literal arrays of size n
 * - r must be an array of n pseudo literals
 *
 * Assert r = (bvsmod a b)
 */
void bit_blaster_make_smod(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *r, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  literal_t *abs_b;
  literal_t *r2, *r3;
  literal_t l, sa, sb, same_sign, z;
  uint32_t i;

  assert(n > 0);

  v = &s->aux_vector2;
  resize_ivector(v, 2 * n);
  ivector_reset(v);
  aux = v->data;
  bvabs_litarray(s, a, aux, n);
  zero_extend_litarray(aux, n); // aux = absolute value of a, zero extended to 2n bits

  v = &s->aux_vector3;
  resize_ivector(v, n);
  ivector_reset(v);
  abs_b = v->data;
  bvabs_litarray(s, b, abs_b, n); // abs_b = absolute value of b

  /*
   * Division: absolute value of a divided by the absolute value of b
   */
  i = n;
  while (i > 0) {
    i --;
    l = bit_blaster_make_bvuge(s, aux+i, abs_b, n);
    bit_blaster_submul(s, aux+i, abs_b, l, n);
  }

  /*
   * At this point aux[n-1 ... 0] contains the remainder r1
   * of the absolute value of a divided by the absolute value of b.
   *
   * There are 5 cases:
   * - if r1=0 then r=0  (b divides a)
   * otherwise
   * - if a>=0 and b>=0 then r = r1
   * - if a>=0 and b<0  then r = b + r1
   * - if a<0  and b>=0 then r = b - r1
   * - if a<0  and b<0  then r = - r1
   *
   * Equivalently, we do:
   * - r2 := if a>=0 then r1 else -r1
   * - same_sign := (sign of a = sign of b)
   * - l := same_sign or (r2 = 0)
   * - r3 := if l then r2 else r2 + b
   * and assert (r = r3).
   */
  sa = a[n-1]; // sign bit of a
  sb = b[n-1]; // sign bit of b
  same_sign = bit_blaster_make_eq(s, sa, sb);

  // build r2
  if (sa == false_literal) { // a >= 0 is true
    r2 = aux;
  } else {
    v = &s->aux_vector4;
    resize_ivector(v, n);
    ivector_reset(v);
    r2 = v->data;
    bvneg_litarray(s, aux, r2, n);              // r2 := neg r1
    bvmux_litarray(s, not(sa), aux, r2, r2, n); // r2 := if a>=0 then r1 else (neg r1)
  }

  // build l := ((sign of a) = (sign of b)) or (r2 = 0)
  if (same_sign == true_literal) {
    l = true_literal;
  } else {
    z = not(bit_blaster_make_or(s, n, r2));
    l = bit_blaster_make_or2(s, same_sign, z);
  }

  // build r3 := (if l then r2 else (r2 + b))
  if (l == true_literal) {
    r3 = r2;
  } else {
    // we reuse aux_vector3 (that currently contains abs_b)
    r3 = abs_b;
    bvadd_litarray(s, r2, b, r3, n);     // r3 := r2 + b
    bvmux_litarray(s, l, r2, r3, r3, n); // r3 := if l then r2 else r2 + b
  }

  // assert r == r3
  assert_pseudo_bveq(s, r, r3, n);
}




/**************
 *  SHIFTERS  *
 *************/

/*
 * In a shifter (shift a b) where a and b are bitvector of size n,
 * then we consider b[0 ... w-1] as 'control bits', where w is such
 * that 2^(w-1) < n <= 2^w.  Any shift amount between 0 and
 * n-1 can be stored using the w lower-order bits of b.
 *
 * Any shift amount larger than or equal to n is considered an overflow.
 *
 * Examples:
 * - n=1 --> no control bits, overflow occurs if b[0] is 1.
 * - n=2 --> 1 control bit b[0] + overflow occurs if b[1] is 1.
 * - n=3 --> 2 control bits b[0] and b[1]. Overflow occurs if b[2] is 1.
 *
 * In general:
 * - n = number of bits
 * - w = number of control bits (we have 0 <= w < n)
 * - overflow occurs if either one of b[w] ... b[n-1] is 1
 *   or the shift amount encoded in the control bits is larger than
 *   or equal to n.
 */
static uint32_t shifter_num_control_bits(uint32_t n) {
  uint32_t w, p;

  assert(n > 0);

  p = 1;
  w = 0;
  while (p < n) {
    w ++;
    p <<= 1;
  }
  return w;
}


/*
 * Given a literal array b and w = number of control bits of b.
 * Compute the minimal shift = constant part of the shift.
 */
static uint32_t shifter_fixed_part(bit_blaster_t *s, literal_t *b, uint32_t w) {
  uint32_t fixed, i, p;
  literal_t l;

  fixed = 0;
  p = 1;
  for (i=0; i<w; i++) {
    l = eval_literal(s, b[i]);
    if (l == true_literal) {
      fixed += p;
    }
    p <<= 1;
  }

  return fixed;
}


/*
 * Check whether literal l = bit of the control input is active
 * - l is inactive if it's true or false in the core
 * - if l is false, then it's ignored in the shift circuit
 * - if l is true, then its contribution to the shift is constant
 *   and part of the amount returned by shifter_fixed_part.
 */
static bool shifter_control_bit_is_active(bit_blaster_t *s, literal_t c) {
  switch (base_value(s, c)) {
  case VAL_FALSE:
  case VAL_TRUE:
    return false;

  default:
    return true;
  }
}


/*
 * Given literal array b and w = number of control bits in b.
 * - find the index k of the last non-constant bit in b and return k+1
 * - return 0 if all bits of b[0...w-1] are constant
 * - return w if b[w-1] is non constant, etc.
 */
static uint32_t shifter_last_control_bit(bit_blaster_t *s, literal_t *b, uint32_t w) {
  while (w > 0) {
    if (shifter_control_bit_is_active(s, b[w-1])) {
      break;
    }
    w --;
  }
  return w;
}


/*
 * Construct l = (bv-or b[w, ... n-1]).
 * If l is true then the shift amount is at least 2^w (>= n).
 */
static inline literal_t shifter_overflow(bit_blaster_t *s, literal_t *b, uint32_t n, uint32_t w) {
  assert(0 <= w && w < n);
  return bit_blaster_make_or(s, n - w, b + w);
}


/*
 * Assert u = [l, ..., l] for a (padding) literal l
 * - u must be an array of n pseudo literals
 */
static void assert_shift_overflow(bit_blaster_t *s, literal_t *u, uint32_t n, literal_t l) {
  remap_table_t *rmap;
  literal_t f;
  uint32_t i;

  rmap = s->remap;
  for (i=0; i<n; i++) {
    f = remap_table_find(rmap, u[i]);
    if (f == null_literal) {
      remap_table_assign(rmap, u[i], l);
    } else {
      bit_blaster_eq(s, f, l);
    }
  }
}


/*
 * Assert u = (ite overflow [l,...,l] a) for a literal l
 * - u must be an array of n pseudo literals
 * - a must be an array of n literals
 */
static void assert_conditional_shift_overflow(bit_blaster_t *s, literal_t *u, literal_t overflow,
                                              literal_t *a, uint32_t n, literal_t l) {
  uint32_t i;

  for (i=0; i<n; i++) {
    assert_pseudo_mux(s, overflow, l, a[i], u[i]); // u[i] == (ite overflow l a[i])
  }
}




/*
 * LEFT SHIFT/PADDING WITH ZEROS
 */

/*
 * Compute d := shift a left by k bits
 */
static void shift_left_by_constant(literal_t *d, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;

  assert(0 <= k && k < n);
  i = n;
  while (i > k) {
    i--;
    d[i] = a[i-k];
  }
  while (i > 0) {
    i --;
    d[i] = false_literal;
  }
}

/*
 * Conditional shift by k bits, depending on control bit b:
 * Compute d := (ite b (a << k) a).
 */
static void conditional_shift_left(bit_blaster_t *s, literal_t *d, literal_t b, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;
  literal_t l;

  assert(0 <= k && k < n);
  i = n;
  while (i > k) {
    i --;
    // d[i] = (ite b a[i-k] a[i])
    l = find_mux(s, b, a[i-k], a[i]);
    if (l == null_literal) {
      l = bit_blaster_fresh_literal(s);
      make_mux(s, b, a[i-k], a[i], l);
    }
    d[i] = l;
  }
  while (i > 0) {
    i --;
    // d[i] = (ite b false_literal a[i])
    l = find_mux(s, b, false_literal, a[i]);
    if (l == null_literal) {
      l = bit_blaster_fresh_literal(s);
      make_mux(s, b, false_literal, a[i], l);
    }
    d[i] = l;
  }
}


/*
 * Assert u = (ite b (a << k) a):
 * - u must be an array of n pseudo literals
 * - a must be an array of n literals
 */
static void assert_conditional_shift_left(bit_blaster_t *s, literal_t *u, literal_t b, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;

  assert(0 <= k && k < n);

  i = n;
  while (i > k) {
    i --;
    assert_pseudo_mux(s, b, a[i-k], a[i], u[i]); // assert u[i] = (ite b a[i-k] a[i]);
  }
  while (i > 0) {
    i --;
    assert_pseudo_mux(s, b, false_literal, a[i], u[i]); // u[i] == (ite b false a[i])
  }
}




/*
 * Assert u = (bvshl a b)
 * - a and b must be arrays of n literals
 * - u must be an array of n pseudo-literals
 *
 * n must be positive
 */
void bit_blaster_make_shift_left(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  literal_t overflow;
  literal_t c;
  uint32_t w, fixed_part;
  uint32_t i, k, shift;

  assert(n > 0);

  w = shifter_num_control_bits(n);
  fixed_part = shifter_fixed_part(s, b, w);
  if (fixed_part >= n) {
    assert_shift_overflow(s, u, n, false_literal); // u = 0b000...00
    return;
  }

  overflow = shifter_overflow(s, b, n, w);
  if (overflow == true_literal) {
    assert_shift_overflow(s, u, n, false_literal); // u = 0b00...00
    return;
  }

  // prepare aux array
  v = &s->aux_vector2;
  resize_ivector(v, n);
  ivector_reset(v);
  aux = v->data;

  // aux := (a << fixed_part)
  shift_left_by_constant(aux, a, n, fixed_part);

  // number of non-fixed control bits
  k = shifter_last_control_bit(s, b, w);


  /*
   * The control bits form a subset of b[0 .. k-1]
   */
  if (overflow == false_literal) {
    if (k == 0) {
      // all controls are constant
      // (bvshl a b) is equal to aux = (a << fixed_part)
      assert_pseudo_bveq(s, u, aux, n); // u = aux

    } else {
      // process control bits from b[0] to b[k-2]
      shift = 1;
      for (i=0; i<k-1; i++) {
        c = b[i];
	if (shifter_control_bit_is_active(s, c)) {
          // aux := (ite c (aux << 2^i) aux)
          conditional_shift_left(s, aux, c, aux, n, shift);
        }
        shift <<= 1;
      }

      // last stage: assert (u == (ite c (aux << 2^(k-1)) aux)
      c = b[k-1];
      assert(shifter_control_bit_is_active(s, c));
      assert_conditional_shift_left(s, u, c, aux, n, shift);
    }

  } else {
    // overflow may be true

    // process all control bits
    shift = 1;
    for (i=0; i<k; i++) {
      c = b[i];
      if (shifter_control_bit_is_active(s, c)) {
        // aux := (ite c (aux << 2^i) aux)
        conditional_shift_left(s, aux, c, aux, n, shift);
      }
      shift <<= 1;
    }

    // last stage: assert (u == (ite overflow 0b00..0 aux))
    assert_conditional_shift_overflow(s, u, overflow, aux, n, false_literal);
  }

}



/*
 * LOGICAL SHIFT RIGHT/PADDING WITH ZEROS
 */

/*
 * Compute d := shift a right by k bits, padding with 0
 */
static void lshift_right_by_constant(literal_t *d, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;

  assert(0 <= k && k < n);
  for (i=0; i<n-k; i++) {
    d[i] = a[i+k];
  }
  while (i<n) {
    d[i] = false_literal;
    i ++;
  }
}

/*
 * Conditional shift right by k bits, depending on control bit b:
 * Compute d := (ite b (a >> k) a).
 */
static void conditional_lshift_right(bit_blaster_t *s, literal_t *d, literal_t b, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;
  literal_t l;

  assert(0 <= k && k < n);

  for (i=0; i<n-k; i++) {
    // d[i] = (ite b a[i+k] a[i])
    l = find_mux(s, b, a[i+k], a[i]);
    if (l == null_literal) {
      l = bit_blaster_fresh_literal(s);
      make_mux(s, b, a[i+k], a[i], l);
    }
    d[i] = l;
  }

  while (i < n) {
    // d[i] = (ite b false_literal a[i])
    l = find_mux(s, b, false_literal, a[i]);
    if (l == null_literal) {
      l = bit_blaster_fresh_literal(s);
      make_mux(s, b, false_literal, a[i], l);
    }
    d[i] = l;
    i++;
  }
}



/*
 * Assert u = (ite b (a >> k) a):
 * - u must be an array of n pseudo literals
 * - a must be an array of n literals
 */
static void assert_conditional_lshift_right(bit_blaster_t *s, literal_t *u, literal_t b, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;

  assert(0 <= k && k < n);

  for (i=0; i<n-k; i++) {
    // u[i] == (ite b a[i+k] a[i])
    assert_pseudo_mux(s, b, a[i+k], a[i], u[i]);
  }
  while (i < n) {
    // u[i] == (ite b false_literal a[i])
    assert_pseudo_mux(s, b, false_literal, a[i], u[i]);
    i ++;
  }
}


/*
 * Assert u = (bvlshr a b): logical shift right
 * - a and b must be arrays of n literals
 * - u must be an array of n pseudo-literals
 *
 * n must be positive
 */
void bit_blaster_make_lshift_right(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  literal_t overflow;
  literal_t c;
  uint32_t w, fixed_part;
  uint32_t i, k, shift;

  assert(n > 0);

  w = shifter_num_control_bits(n);
  fixed_part = shifter_fixed_part(s, b, w);
  if (fixed_part >= n) {
    assert_shift_overflow(s, u, n, false_literal); // u = 0b000...00
    return;
  }

  overflow = shifter_overflow(s, b, n, w);
  if (overflow == true_literal) {
    assert_shift_overflow(s, u, n, false_literal); // u = 0b00...00
    return;
  }

  // prepare aux array
  v = &s->aux_vector2;
  resize_ivector(v, n);
  ivector_reset(v);
  aux = v->data;

  // aux := (a >> fixed_part)
  lshift_right_by_constant(aux, a, n, fixed_part);

  // number of non-constant control bits
  k = shifter_last_control_bit(s, b, w);


  /*
   * The control bits form a subset of b[0 .. k-1]
   */
  if (overflow == false_literal) {
    if (k == 0) {
      // all controls are constant
      // (bvshl a b) is equal to aux = (a << fixed_part)
      assert_pseudo_bveq(s, u, aux, n); // u = aux

    } else {
      // process control bits from b[0] to b[k-2]
      shift = 1;
      for (i=0; i<k-1; i++) {
        c = b[i];
	if (shifter_control_bit_is_active(s, c)) {
          // aux := (ite c (aux << 2^i) aux)
          conditional_lshift_right(s, aux, c, aux, n, shift);
        }
        shift <<= 1;
      }

      // last stage: assert (u == (ite c (aux << 2^(k-1)) aux)
      c = b[k-1];
      assert(shifter_control_bit_is_active(s, c));
      assert_conditional_lshift_right(s, u, c, aux, n, shift);
    }

  } else {
    // overflow may be true

    // process all control bits
    shift = 1;
    for (i=0; i<k; i++) {
      c = b[i];
      if (shifter_control_bit_is_active(s, c)) {
        // aux := (ite c (aux << 2^i) aux)
        conditional_lshift_right(s, aux, c, aux, n, shift);
      }
      shift <<= 1;
    }

    // last stage: assert (u == (ite overflow 0b00..0 aux))
    assert_conditional_shift_overflow(s, u, overflow, aux, n, false_literal);
  }

}




/*
 * ARITHMETIC SHIFT RIGHT
 */

/*
 * Compute d := shift a right by k bits, padding with sign bit
 */
static void ashift_right_by_constant(literal_t *d, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;
  literal_t sgn;

  assert(0 <= k && k < n);
  for (i=0; i<n-k; i++) {
    d[i] = a[i+k];
  }
  sgn = a[n-1];
  while (i<n) {
    d[i] = sgn;
    i ++;
  }
}

/*
 * Conditional shift right by k bits, depending on control bit b:
 * Compute d := (ite b (a >> k) a).
 */
static void conditional_ashift_right(bit_blaster_t *s, literal_t *d, literal_t b, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;
  literal_t l, sgn;

  assert(0 <= k && k < n);

  for (i=0; i<n-k; i++) {
    // d[i] = (ite b a[i+k] a[i])
    l = find_mux(s, b, a[i+k], a[i]);
    if (l == null_literal) {
      l = bit_blaster_fresh_literal(s);
      make_mux(s, b, a[i+k], a[i], l);
    }
    d[i] = l;
  }

  sgn = a[n-1]; // sign bit of a
  while (i < n) {
    // d[i] = (ite b sgn a[i])
    l = find_mux(s, b, sgn, a[i]);
    if (l == null_literal) {
      l = bit_blaster_fresh_literal(s);
      make_mux(s, b, sgn, a[i], l);
    }
    d[i] = l;
    i++;
  }
}



/*
 * Assert u = (ite b (a >> k) a):
 * - u must be an array of n pseudo literals
 * - a must be an array of n literals
 */
static void assert_conditional_ashift_right(bit_blaster_t *s, literal_t *u, literal_t b, literal_t *a, uint32_t n, uint32_t k) {
  uint32_t i;
  literal_t sgn;

  assert(0 <= k && k < n);

  for (i=0; i<n-k; i++) {
    // u[i] == (ite b a[i+k] a[i])
    assert_pseudo_mux(s, b, a[i+k], a[i], u[i]);
  }
  sgn = a[n-1];
  while (i < n) {
    // u[i] == (ite b sgn a[i])
    assert_pseudo_mux(s, b, sgn, a[i], u[i]);
    i ++;
  }
}


/*
 * Assert u = (bvashr a b): arithmetic shift right
 * - a and b must be arrays of n literals
 * - u must be an array of n pseudo-literals
 *
 * n must be positive
 */
void bit_blaster_make_ashift_right(bit_blaster_t *s, literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  ivector_t *v;
  literal_t *aux;
  literal_t overflow;
  literal_t sgn;
  literal_t c;
  uint32_t w, fixed_part;
  uint32_t i, k, shift;

  assert(n > 0);

  sgn = a[n-1];

  w = shifter_num_control_bits(n);
  fixed_part = shifter_fixed_part(s, b, w);
  if (fixed_part >= n) {
    assert_shift_overflow(s, u, n, sgn); // u = sign bit copied n times
    return;
  }

  overflow = shifter_overflow(s, b, n, w);
  if (overflow == true_literal) {
    assert_shift_overflow(s, u, n, sgn); // u = sign bit copied n times
    return;
  }

  // prepare aux array
  v = &s->aux_vector2;
  resize_ivector(v, n);
  ivector_reset(v);
  aux = v->data;

  // aux := (a >> fixed_part)
  ashift_right_by_constant(aux, a, n, fixed_part);

  // number of control bits
  k = shifter_last_control_bit(s, b, w);


  /*
   * The control bits form a subset of b[0 .. k-1]
   */
  if (overflow == false_literal) {
    if (k == 0) {
      // all controls are constant
      // (bvshl a b) is equal to aux = (a << fixed_part)
      assert_pseudo_bveq(s, u, aux, n); // u = aux

    } else {
      // process control bits from b[0] to b[k-2]
      shift = 1;
      for (i=0; i<k-1; i++) {
        c = b[i];
	if (shifter_control_bit_is_active(s, c)) {
          // aux := (ite c (aux << 2^i) aux)
          conditional_ashift_right(s, aux, c, aux, n, shift);
        }
        shift <<= 1;
      }

      // last stage: assert (u == (ite c (aux << 2^(k-1)) aux)
      c = b[k-1];
      assert(shifter_control_bit_is_active(s, c));
      assert_conditional_ashift_right(s, u, c, aux, n, shift);
    }

  } else {
    // overflow may be true

    // process all control bits
    shift = 1;
    for (i=0; i<k; i++) {
      c = b[i];
      if (shifter_control_bit_is_active(s, c)) {
	// aux := (ite c (aux << 2^i) aux)
        conditional_ashift_right(s, aux, c, aux, n, shift);
      }
      shift <<= 1;
    }

    // last stage: assert (u == (ite overflow [sgn ... sgn] aux))
    assert_conditional_shift_overflow(s, u, overflow, aux, n, sgn);
  }

}





/***********
 *  TRACE  *
 **********/

#if TRACE

static void trace_cbuffer(cbuffer_t *buffer) {
  literal_t aux[CBUFFER_NVARS];
  uint32_t i, n, k;

  if (buffer->is_unsat) {
    printf("Unsat\n");
  } else {
    n = buffer->nclauses;
    if (n == 0) {
      printf("No clauses\n");
    } else {
      printf("Clauses:\n");
      for (i=0; i<n; i++) {
        k = cbuffer_extract_clause(buffer, i, aux);
        int_array_sort(aux, k);
        print_litarray(stdout, k, aux);
        printf("\n");
      }
      printf("----\n");
    }
  }
}


static void trace_clause(uint32_t n, literal_t *a) {
  print_litarray(stdout, n, a);
  printf("\n");
}

static void trace_unit_clause(bit_blaster_t *s, literal_t a) {
  switch (base_value(s, a)) {
  case VAL_FALSE:
    printf("{}\n");
    break;
  case VAL_UNDEF_FALSE:
  case VAL_UNDEF_TRUE:
    printf("{");
    print_literal(stdout, a);
    printf("}\n");
    break;
  case VAL_TRUE:
  default:
    printf("redundant {");
    print_literal(stdout, a);
    printf("}\n");
    break;
  }
}

static void trace_binary_clause(literal_t a, literal_t b) {
  printf("{");
  print_literal(stdout, a);
  printf(" ");
  print_literal(stdout, b);
  printf("}\n");
}

static void trace_ternary_clause(literal_t a, literal_t b, literal_t c) {
  printf("{");
  print_literal(stdout, a);
  printf(" ");
  print_literal(stdout, b);
  printf(" ");
  print_literal(stdout, c);
  printf("}\n");
}

static void trace_quad_clause(literal_t a, literal_t b, literal_t c, literal_t d) {
  printf("{");
  print_literal(stdout, a);
  printf(" ");
  print_literal(stdout, b);
  printf(" ");
  print_literal(stdout, c);
  printf(" ");
  print_literal(stdout, d);
  printf("}\n");
}



#endif
