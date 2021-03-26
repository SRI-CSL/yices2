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
 * ENCODING OF BOOLEAN OPERATORS IN CLAUSAL FORM
 */


#include <stdint.h>
#include <assert.h>

#include "solvers/cdcl/gates_manager.h"
#include "utils/int_array_sort.h"

/*
 * Initialize manager m
 * - core = attached core solver
 */
void init_gate_manager(gate_manager_t *m, smt_core_t *core) {
  m->core = core;
  m->htbl = get_gate_table(core);
  init_ivector(&m->buffer, 0);
}


/*
 * Delete hash table and buffer
 */
void delete_gate_manager(gate_manager_t *m) {
  m->core = NULL;
  m->htbl = NULL;
  delete_ivector(&m->buffer);
}



/**********************
 *  OR AND AND GATES  *
 *********************/

/*
 * Assert clauses for l == (OR a[0] ... a[n-1])
 * - the literals a[0] ... a[n-1] are stored in vector v
 * - v is modified
 */
static void assert_ordef_clauses(smt_core_t *s, literal_t l, ivector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    add_binary_def_clause(s, var_of(l), l, not(v->data[i]));
  }

  ivector_push(v, not(l));
  add_def_clause(s, var_of(l), n+1, v->data);
}


/*
 * Construct OR based on the content of vector v
 * - v should not contain false literals (or true literals)
 * - tbl = gate table
 * - s = smt core
 */
static literal_t aux_or_constructor(gate_table_t *tbl, smt_core_t *s, ivector_t *v) {
  uint32_t i, n, p;
  literal_t aux, l;
  literal_t *a;
  boolgate_t *g;

  n = v->size;
  a = v->data;

  if (n == 0) return false_literal;

  /*
   * Sort, remove duplicates, check for complementary literals
   */
  int_array_sort(a, n);
  l = a[0];
  p = 1;
  for (i=1; i<n; i++) {
    aux = a[i];
    if (aux != l) {
      if (aux == not(l)) return true_literal; // (or .. l not(l) ..)
      a[p++] = aux;
      l = aux;
    }
  }

  if (p == 1) return a[0];
  ivector_shrink(v, p);

  if (p <= MAX_HASHCONS_SIZE) {
    // hash-consing
    g = gate_table_get(tbl, orgate_tag(p), a);
    l = g->lit[p];  // output literal for an or-gate
    if (l == null_literal) {
      // new gate: create a fresh literal l
      l = pos_lit(create_boolean_variable(s));
      g->lit[p] = l;
      assert_ordef_clauses(s, l, v);
    }

  } else {
    // no hash-consing
    l = pos_lit(create_boolean_variable(s));
    assert_ordef_clauses(s, l, v);
  }

  return l;
}


/*
 * OR GATE
 */
literal_t mk_or_gate(gate_manager_t *m, uint32_t n, literal_t *a) {
  smt_core_t *s;
  ivector_t *v;
  literal_t l;
  uint32_t i;

  s = m->core;
  v = &m->buffer;
  ivector_reset(v);

  /*
   * Remove false literals/check for true literals
   * - copy unassigned literals in the buffer
   */
  for (i = 0; i<n; i++) {
    l = a[i];
    switch (literal_base_value(s, l)) {
    case VAL_FALSE:
      break;
    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      ivector_push(v, l);
      break;
    case VAL_TRUE:
      return true_literal;
    }
  }

  return aux_or_constructor(m->htbl, s, v);
}

literal_t mk_or_gate2(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t a[2];

  a[0] = l1;
  a[1] = l2;
  return mk_or_gate(m, 2, a);
}

literal_t mk_or_gate3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3) {
  literal_t a[3];

  a[0] = l1;
  a[1] = l2;
  a[2] = l3;
  return mk_or_gate(m, 3, a);
}





/*
 * AND GATE
 */
literal_t mk_and_gate(gate_manager_t *m, uint32_t n, literal_t *a) {
  smt_core_t *s;
  ivector_t *v;
  literal_t l;
  uint32_t i;

  s = m->core;
  v = &m->buffer;
  ivector_reset(v);

  /*
   * Remove true literals/check for false literals
   * - copy negation of unassigned literals in the buffer
   */
  for (i = 0; i<n; i++) {
    l = a[i];
    switch (literal_base_value(s, l)) {
    case VAL_FALSE:
      return false_literal;
    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      ivector_push(v, not(l));
      break;
    case VAL_TRUE:
      break;
    }
  }

  return not(aux_or_constructor(m->htbl, s, v));
}


literal_t mk_and_gate2(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t a[2];

  a[0] = l1;
  a[1] = l2;
  return mk_and_gate(m, 2, a);
}

literal_t mk_and_gate3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3) {
  literal_t a[3];

  a[0] = l1;
  a[1] = l2;
  a[2] = l3;
  return mk_and_gate(m, 3, a);
}




/***************
 *  XOR GATES  *
 **************/

/*
 * Create a literal l and assert clauses equivalent to l=(xor l1 l2)
 */
static literal_t assert_xordef2(smt_core_t *s, literal_t l1, literal_t l2) {
  bvar_t x;
  literal_t l;

  x = create_boolean_variable(s);
  l = pos_lit(x);
  add_ternary_def_clause(s, x, not(l1), not(l2), not(l));
  add_ternary_def_clause(s, x, not(l1), l2, l);
  add_ternary_def_clause(s, x, l1, not(l2), l);
  add_ternary_def_clause(s, x, l1, l2, not(l));
  return l;
}

/*
 * Create a literal l and assert clauses for l = (xor a[0] ... a[n-1])
 * - v = vector a[0] ... a[n-1]
 * - assumptions: v contains not false or true literals, no duplicate,
 *   and no pairs of complementary literals
 * - n must be positive
 */
static literal_t assert_xordef_clauses(smt_core_t *s, ivector_t *v) {
  uint32_t i, n;
  literal_t *a;
  literal_t l;

  n = v->size;
  a = v->data;

  assert(n > 0);

  l = a[0];
  for (i=1; i<n; i++) {
    l = assert_xordef2(s, l, a[i]);
  }
  return l;
}

/*
 * Simplify (XOR a[0] ... a[n-1])
 * - the result is given by vector v and the returned integer
 * - the returned value is either 0 or 1
 * - if it's 0 the result is (XOR v[0] ... v[p-1])
 * - if it's 1 the result is not (XOR v[0] ... v[p-1])
 *
 * HACK: the simplifications use bit-tricks that are dependent
 * on the literal representation, namely,
 * low-order bit = 0 for positive literals
 * low-order bit = 1 for negative literals
 */
static uint32_t simplify_xor(smt_core_t *s, uint32_t n, literal_t *a, ivector_t *v) {
  uint32_t i, sgn, p;
  literal_t l;

  ivector_reset(v);
  sgn = 0;

  // remove true/false literals and negative literals
  for (i=0; i<n; i++) {
    l = a[i];
    switch (literal_base_value(s, l)) {
    case VAL_FALSE:
      break;
    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      sgn ^= sign_of_lit(l);  // flip sgn if l is negative
      l &= ~1;                // remove sign = low-order bit
      ivector_push(v, l);
      break;
    case VAL_TRUE:
      sgn ^= 1;
      break;
    }
  }

  a = v->data;
  n = v->size;

  if (n > 0) {
    // remove duplicates (i.e., apply the rule (XOR x x) == 0)
    int_array_sort(a, n);
    p = 0;
    i = 0;
    while (i<n-1) {
      l = a[i];
      if (l == a[i+1]) {
        i += 2;
      } else {
        a[p++] = l;
        i ++;
      }
    }
    if (i == n-1) {
      a[p++] = a[i];
    }
    ivector_shrink(v, p);
  }

  return sgn;
}

/*
 * Simplify then create l = (XOR a[0] ... a[n-1])
 */
literal_t mk_xor_gate(gate_manager_t *m, uint32_t n, literal_t *a) {
  smt_core_t *s;
  ivector_t *v;
  literal_t l;
  uint32_t sgn;
  boolgate_t *g;

  s = m->core;
  v = &m->buffer;

  sgn = simplify_xor(s, n, a, v);

  a = v->data;
  n = v->size;

  if (n == 0) return false_literal ^ sgn;
  if (n == 1) return a[0] ^ sgn;

  if (n <= MAX_HASHCONS_SIZE) {
    g = gate_table_get(m->htbl, xorgate_tag(n), a);
    l = g->lit[n];
    if (l == null_literal) {
      l = assert_xordef_clauses(s, v);
      g->lit[n] = l;
    }
  } else {
    l = assert_xordef_clauses(s, v);
  }

  return l ^ sgn;
}


literal_t mk_xor_gate2(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t a[2];

  a[0] = l1;
  a[1] = l2;
  return mk_xor_gate(m, 2, a);
}

literal_t mk_xor_gate3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3) {
  literal_t a[3];

  a[0] = l1;
  a[1] = l2;
  a[2] = l3;
  return mk_xor_gate(m, 3, a);
}


/*
 * Assert (XOR l1 l2)
 */
static void assert_xor2_clauses(smt_core_t *s, literal_t l1, literal_t l2) {
  add_binary_clause(s, l1, l2);
  add_binary_clause(s, not(l1), not(l2));
}

/*
 * Assert (XOR l1 l2 l3) == true
 */
static void assert_xor3_clauses(smt_core_t *s, literal_t l1, literal_t l2, literal_t l3) {
  add_ternary_clause(s, l1, l2, l3);
  add_ternary_clause(s, l1, not(l2), not(l3));
  add_ternary_clause(s, not(l1), l2, not(l3));
  add_ternary_clause(s, not(l1), not(l2), l3);
}


/*
 * Assertion of (XOR a[0] ... a[n-1]) == true/false
 */
void assert_xor(gate_manager_t *m, uint32_t n, literal_t *a, bool val) {
  smt_core_t *s;
  ivector_t *v;
  uint32_t i, sgn;
  literal_t l;

  s = m->core;
  v = &m->buffer;
  sgn = simplify_xor(s, n, a, v);
  a = v->data;
  n = v->size;

  if (sgn == 1) {
    val = ! val;
  }

  if (n == 0) {
    // empty (XOR ..) is false_literal
    if (val) add_empty_clause(s);
    return;
  }

  // (not (XOR a[0] ... a[n-1])) <=> (XOR (not a[0]) ... a[n-1])
  if (! val) {
    a[0] = not(a[0]);
  }

  if (n == 1) {
    add_unit_clause(s, a[0]);
  } else if (n == 2) {
    assert_xor2_clauses(s, a[0], a[1]);
  } else {
    l = a[2];
    for (i=3; i<n; i++) {
      l = assert_xordef2(s, l, a[i]);
    }
    assert_xor3_clauses(s, a[0], a[1], l);
  }

}

void assert_xor2(gate_manager_t *m, literal_t l1, literal_t l2, bool val) {
  literal_t a[2];

  a[0] = l1;
  a[1] = l2;
  assert_xor(m, 2, a, val);
}

void assert_xor3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3, bool val) {
  literal_t a[3];

  a[0] = l1;
  a[1] = l2;
  a[2] = l3;
  assert_xor(m, 3, a, val);
}



/************************
 * BOOLEAN IF-THEN-ELSE *
 ***********************/

/*
 * Construct l = (ite c l1 l2) (or find it in the gate table)
 */
static literal_t mk_ite_aux(gate_manager_t *m, literal_t c, literal_t l1, literal_t l2) {
  smt_core_t *s;
  boolgate_t *g;
  literal_t a[3], l;
  bvar_t x;

  a[0] = c;
  a[1] = l1;
  a[2] = l2;
  g = gate_table_get(m->htbl, itegate_tag(), a);
  l = g->lit[3];
  if (l == null_literal) {
    s = m->core;
    x = create_boolean_variable(s);
    l = pos_lit(x);
    g->lit[3] = l;
    add_ternary_def_clause(s, x, not(l), c, l2);
    add_ternary_def_clause(s, x, not(l), not(c), l1);
    add_ternary_def_clause(s, x, l, c, not(l2));
    add_ternary_def_clause(s, x, l, not(c), not(l1));

    /*
     * Redundant clauses that may help propagation:
     * (l1 and l2 ==> l)
     * (not l1 and not l2 ==> not l)
     */
#if 0
    add_ternary_clause(s, not(l1), not(l2), l);
    add_ternary_clause(s, l1, l2, not(l));
#endif
  }
  return l;
}


/*
 * Normalize: make sure c and l are positive literals in (ite c l1 l2)
 * Rules:
 *  (ite (not c) l1 l2) --> (ite c l2 l1)
 *  (ite c (not l1) l2) --> (not (ite c l1 (not l2)))
 */
static literal_t mk_ite_aux2(gate_manager_t *m, literal_t c, literal_t l1, literal_t l2) {
  literal_t aux;

  if (is_neg(c)) {
    c = not(c);
    aux = l1; l1 = l2; l2 = aux; // swap l1 and l2
  }

  if (is_neg(l1)) {
    return not(mk_ite_aux(m, c, not(l1), not(l2)));
  } else {
    return mk_ite_aux(m, c, l1, l2);
  }
}


/*
 * Simplify then generate l = (ite c l1 l2)
 */
literal_t mk_ite_gate(gate_manager_t *m, literal_t c, literal_t l1, literal_t l2) {
  smt_core_t *s;
  bval_t v1, v2;

  s = m->core;

  switch (literal_base_value(s, c)) {
  case VAL_FALSE:
    return l2;
  case VAL_UNDEF_FALSE:
  case VAL_UNDEF_TRUE:
    /*
     * (ite c l l) == l
     * (ite c l (not l)) == (iff c l) --> CHECK THIS: not clear that it helps
     *
     * (ite c c l2) == (ite c true l2) == (or c l2)
     * (ite c l1 c) == (ite c l1 false) == (and c l1)
     * (ite c (not c) l2) == (ite c false l2) == (and (not c) l2)
     * (ite c l1 (not c)) == (ite c l1 true) == (or (not c) l1)
     */
    if (l1 == l2) return l1;
    if (opposite(l1, l2)) return mk_iff_gate(m, c, l1);

    v1 = literal_base_value(s, l1);
    v2 = literal_base_value(s, l2);
    if (c == l1 || v1 == VAL_TRUE)  return mk_or_gate2(m, c, l2);
    if (c == l2 || v2 == VAL_FALSE) return mk_and_gate2(m, c, l1);
    if (c == not(l1) || v1 == VAL_FALSE) return mk_and_gate2(m, not(c), l2);
    if (c == not(l2) || v2 == VAL_TRUE)  return mk_or_gate2(m, not(c), l1);

    return mk_ite_aux2(m, c, l1, l2);

  case VAL_TRUE:
  default: // prevents compilation warning
    return l1;
  }
}


/*
 * Assert (ite c l1 l2) == val
 * - val is true or false
 */
void assert_ite(gate_manager_t *m, literal_t c, literal_t l1, literal_t l2, bool val) {
  smt_core_t *s;
  bval_t v1, v2;

  if (! val) {
    l1 = not(l1);
    l2 = not(l2);
  }

  s = m->core;

  if (l1 == l2) {
    add_unit_clause(s, l1);
  } else {
    /*
     * We need two clauses: (or (not c) l1) and (or c l2)
     * It's marginally better to simplify them here than let
     * smt_core do it (because we avoid unit propagation).
     */
    switch (literal_base_value(s, c)) {
    case VAL_FALSE:
      add_unit_clause(s, l2);
      break;

    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      v1 = literal_base_value(s, l1);
      v2 = literal_base_value(s, l2);
      if (c == l1 || v1 == VAL_TRUE)  {
        add_binary_clause(s, c, l2); // assert (or c l2)
        break;
      }
      if (c == l2 || v2 == VAL_FALSE) {
        add_unit_clause(s, c);
        add_unit_clause(s, l1); // assert (and c l1)
        break;
      }
      if (c == not(l1) || v1 == VAL_FALSE) {
        add_unit_clause(s, not(c));
        add_unit_clause(s, l2); // assert (and (not c) l2)
        break;
      }
      if (c == not(l2) || v2 == VAL_TRUE)  {
        add_binary_clause(s, not(c), l1); // assert (or (not c) l1)
        break;
      }

      add_binary_clause(s, not(c), l1);
      add_binary_clause(s, c, l2);
#if 0
      // redundant clause that may help ?
      add_binary_clause(s, l1, l2);
#endif
      break;

    case VAL_TRUE:
      add_unit_clause(s, l1);
      break;
    }
  }
}
