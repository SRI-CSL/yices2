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
 * TABLE OF BOOLEAN VARIABLES
 */

#include <assert.h>

#include "scratch/bool_vartable.h"
#include "utils/bit_tricks.h"
#include "utils/hash_functions.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"


/*
 * ARRAY OF GATE DESCRIPTORS
 */
static void init_bgate_array(bgate_array_t *a) {
  a->data = NULL;
  a->ngates = 0;
  a->size = 0;
}

static void extend_bgate_array(bgate_array_t *a) {
  uint32_t n;

  n = a->size;
  if (n == 0) {
    n = DEF_BGATE_ARRAY_SIZE; // first allocation
    assert(n <= MAX_BGATE_ARRAY_SIZE);
    a->data = (bgate_t *) safe_malloc(n * sizeof(bgate_array_t));
    a->size = n;
  } else {
    // try to make the table 50% larger
    n += (n >> 1);
    assert(n > a->size);
    if (n > MAX_BGATE_ARRAY_SIZE) {
      out_of_memory();
    }

    a->data = (bgate_t *) safe_realloc(a->data, n * sizeof(bgate_array_t));
    a->size = n;
  }
}

static void delete_bgate_array(bgate_array_t *a) {
  safe_free(a->data);
  a->data = NULL;
}

static void reset_bgate_array(bgate_array_t *a) {
  a->ngates = 0;
}


/*
 * Copy g as a new descriptor in a
 * - return the index of the newly allocated element
 */
static uint32_t store_bgate(bgate_array_t *a, bgate_t *g) {
  uint32_t i;

  i = a->ngates;
  if (i == a->size) {
    extend_bgate_array(a);
  }
  assert(i < a->size);
  a->data[i] = *g;
  a->ngates = i+1;

  return i;
}




/*
 * DESCRIPTORS FOR OR GATES
 */
static void init_ordata_array(ordata_array_t *a) {
  a->data = NULL;
  a->top = 0;
  a->size = 0;
}

static void delete_ordata_array(ordata_array_t *a) {
  safe_free(a->data);
  a->data = NULL;
}

static void reset_ordata_array(ordata_array_t *a) {
  a->top = 0;
}


/*
 * Make the array large enough to store n integers
 */
static void ordata_array_resize(ordata_array_t *a, uint32_t n) {
  uint32_t old_size, new_size;

  old_size = a->size;
  if (n < old_size) {
    if (n > MAX_ORDATA_ARRAY_SIZE) {
      out_of_memory();
    }

    if (old_size == 0) {
      /*
       * First allocation: use max(n, default size)
       */
      new_size = DEF_ORDATA_ARRAY_SIZE;
      if (new_size < n) {
        new_size = n;
      }
      assert(new_size <= MAX_ORDATA_ARRAY_SIZE);

      a->data = (uint32_t *) safe_malloc(new_size * sizeof(int32_t));
      a->size = new_size;

    } else {
      /*
       * try to increase the size by 50%
       * if that's not enough, use n
       */
      new_size = old_size;
      new_size += new_size >> 1;
      if (new_size > MAX_ORDATA_ARRAY_SIZE) {
        new_size = MAX_ORDATA_ARRAY_SIZE;
      } else if (new_size < n) {
        new_size = n;
      }

      assert(new_size <= MAX_ORDATA_ARRAY_SIZE && n <= new_size);
      a->data = (uint32_t *) safe_realloc(a->data, new_size * sizeof(int32_t));
      a->size = new_size;
    }
  }
}


/*
 * Copy array b into a
 * - n = number of elements in b
 * - return the index k in a->data where b is copied
 */
static uint32_t store_ordata(ordata_array_t *a, literal_t *b, uint32_t n) {
  uint32_t *aux;
  uint32_t i, k;

  if (n >= MAX_ORDATA_ARRAY_SIZE) {
    out_of_memory();
  }
  // the sum a->top + n + 1 can't overflow
  ordata_array_resize(a, a->top + n + 1);

  assert(a->top + n + 1 <= a->size);

  k = a->top;
  a->data[k] = n; // store arity first

  aux = a->data + k + 1;
  for (i=0; i<n; i++) {
    aux[i] = b[i];
  }

  return k;
}



/*
 * LITERAL VECTORS
 */
static inline void init_lvector(lvector_t *v) {
  v->data = NULL;
  v->nelems = 0;
  v->size = 0;
}

static void delete_lvector(lvector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}

static inline void reset_lvector(lvector_t *v) {
  v->nelems = 0;
}


/*
 * Increase the size of v (when v contains fixed size clauses)
 * - k = size of the clauses in v
 */
static void extend_fixed_lvector(lvector_t *v, uint32_t k) {
  uint32_t n;

  n = v->size;
  if (n == 0) {
    n = k * DEF_CLAUSESET_SIZE;
  } else {
    n += n; // double the size
  }
  assert(n > v->size);

  if (n > MAX_LVECTOR_SIZE) {
    out_of_memory();
  }

  assert((n % k) == 0);
  v->data = (uint32_t *) safe_realloc(v->data, n * sizeof(uint32_t));
  v->size = n;
}


/*
 * Increase v's size: make sure there's room for k more elements in
 * v->data.
 */
static void extend_lvector(lvector_t *v, uint32_t k) {
  uint32_t n;

  n = v->size;
  if (n == 0) {
    n = DEF_LVECTOR_SIZE;
  } else {
    n += (n+1) >> 1;
  }
  if (n < v->size + k) {
    n = v->size + k;
  }

  if (n > MAX_LVECTOR_SIZE) {
    out_of_memory();
  }
  v->data = (uint32_t *) safe_realloc(v->data, n * sizeof(uint32_t));
  v->size = n;
}


/*
 * Store a clause of size k in vector v
 * - v contains fixed-size clauses (all of size k)
 * - a = array of k literals
 */
static void fixed_lvector_add_clause(lvector_t *v, uint32_t k, literal_t *a) {
  uint32_t i, j;
  uint32_t *d;

  i = v->nelems;
  if (i == v->size) {
    extend_fixed_lvector(v, k);
  }
  assert(i + k <= v->size);

  d = v->data + i;
  for (j=0; j<k; j++) {
    d[j] = a[j];
  }
  v->nelems = i + k;
}


/*
 * Same thing when v contains variable-size clauses
 */
static void lvector_add_clause(lvector_t *v, uint32_t k, literal_t *a) {
  uint32_t i, j;
  uint32_t *d;

  i = v->nelems;
  if (i + k + 1 > v->size) {
    extend_lvector(v, k+1);
  }
  assert(i + k + 1 <= v->size);

  d = v->data + i;
  d[0] = k;  // size is stored first
  d ++;
  for (j=0; j<k; j++) {
    d[j] = a[j];
  }

  v->nelems = i + k + 1;
}



/*
 * CLAUSE SET
 */
static void init_clause_set(clause_set_t *cs) {
  uint32_t i;

  for (i=0; i<NUM_CLAUSE_SETS; i++) {
    init_lvector(cs->set + i);
  }
  cs->has_empty_clause = false;
}

static void delete_clause_set(clause_set_t *cs) {
  uint32_t i;

  for (i=0; i<NUM_CLAUSE_SETS; i++) {
    delete_lvector(cs->set + i);
  }
}

static void reset_clause_set(clause_set_t *cs) {
  uint32_t i;

  for (i=0; i<NUM_CLAUSE_SETS; i++) {
    reset_lvector(cs->set + i);
  }
  cs->has_empty_clause = false;
}



/*
 * Add clause a of n literals
 */
static void clause_set_add(clause_set_t *cs, uint32_t k, literal_t *a) {
  if (k == 0) {
    cs->has_empty_clause = true;
  } else if (k < NUM_CLAUSE_SETS) {
    fixed_lvector_add_clause(cs->set + k, k, a); // add in cs->set[k]
  } else {
    lvector_add_clause(cs->set, k, a); // add in cs->set[0]
  }
}


/*
 * Short cuts for n=0, 1, 2, and 3
 */
static inline void clause_set_add_empty_clause(clause_set_t *cs) {
  cs->has_empty_clause = true;
}

static inline void clause_set_add_unit_clause(clause_set_t *cs, literal_t l1) {
  fixed_lvector_add_clause(cs->set + 1, 1, &l1);
}

static inline void clause_set_add_binary_clause(clause_set_t *cs, literal_t l1, literal_t l2) {
  literal_t aux[2];

  aux[0] = l1;
  aux[1] = l2;
  fixed_lvector_add_clause(cs->set + 2, 2, aux);
}

static inline void clause_set_add_ternary_clause(clause_set_t *cs, literal_t l1, literal_t l2, literal_t l3) {
  literal_t aux[3];

  aux[0] = l1;
  aux[1] = l2;
  aux[2] = l3;
  fixed_lvector_add_clause(cs->set + 3, 3, aux);
}


/*
 * EQUALITY QUEUE
 */
static inline void init_equiv_queue(equiv_queue_t *queue) {
  queue->data = NULL;
  queue->top = 0;
  queue->prop_ptr = 0;
  queue->size = 0;
}

static void delete_equiv_queue(equiv_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}

static inline void reset_equiv_queue(equiv_queue_t *queue) {
  queue->top = 0;
  queue->prop_ptr = 0;
}

static void extend_equiv_queue(equiv_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    n = DEF_EQUIV_QUEUE_SIZE;
    assert(n <= MAX_EQUIV_QUEUE_SIZE);
    queue->data = safe_malloc(n * sizeof(equiv_t));
    queue->size = n;
  } else {
    n += (n+1)>>1;
    if (n > MAX_EQUIV_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->data = safe_realloc(queue->data, n * sizeof(equiv_t));
    queue->size = n;
  }
}


/*
 * Add equality l1 == l2 to the queue
 */
static void push_equiv(equiv_queue_t *queue, literal_t l1, literal_t l2) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_equiv_queue(queue);
  }
  assert(i < queue->size);
  queue->data[i].left = l1;
  queue->data[i].right = l2;
  queue->top = i+1;
}





/*
 * HASH FUNCTIONS
 */
static uint32_t hash_bgate(bgate_t *g) {
  return jenkins_hash_quad(g->ttbl, g->var[0], g->var[1], g->var[2], 0xae01781a);
}

static uint32_t hash_orgate(uint32_t n, literal_t *a) {
  return jenkins_hash_intarray2(a, n, 0xfedcba98);
}



/*
 * GLOBAL OPERATIONS ON THE TABLE
 */

/*
 * Initialize the table: this creates variable 0 = true
 */
void init_bool_vartable(bool_vartable_t *table) {
  uint32_t n;

  n = DEF_BOOLVARTABLE_SIZE;
  assert(0 < n && n <= MAX_BOOLVARTABLE_SIZE);

  table->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->desc = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  table->map = (literal_t *) safe_malloc(n * sizeof(literal_t));
  table->root = allocate_bitvector(n);

  assert(0 == const_bvar);

  // 0 is root, mapped to true_literal
  table->tag[0] = BCONST;
  table->desc[0] = 0;
  table->map[0] = true_literal;
  set_bit(table->root, 0);

  table->nvars = 1;
  table->size = n;

  init_bgate_array(&table->gates);
  init_ordata_array(&table->ordata);
  init_clause_set(&table->clauses);
  init_equiv_queue(&table->queue);

  init_int_htbl(&table->htbl, 0);
}


/*
 * Make the table 50% larger
 */
static void extend_bool_vartable(bool_vartable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n > MAX_BOOLVARTABLE_SIZE) {
    out_of_memory();
  }

  table->tag = (uint8_t *) safe_realloc(table->tag, n * sizeof(uint8_t));
  table->desc = (uint32_t *) safe_realloc(table->desc, n * sizeof(uint32_t));
  table->map = (literal_t *) safe_realloc(table->map, n * sizeof(literal_t));
  table->root = extend_bitvector(table->root, n);

  table->size = n;
}


/*
 * Free memory
 */
void delete_bool_vartable(bool_vartable_t *table) {
  safe_free(table->tag);
  safe_free(table->desc);
  safe_free(table->map);
  delete_bitvector(table->root);
  table->tag = NULL;
  table->desc = NULL;
  table->map = NULL;
  table->root = NULL;
  delete_bgate_array(&table->gates);
  delete_ordata_array(&table->ordata);
  delete_clause_set(&table->clauses);
  delete_equiv_queue(&table->queue);
  delete_int_htbl(&table->htbl);
}


/*
 * Reset: empty the table. All variables and descriptors are
 * removed except variable 0.
 */
void reset_bool_vartable(bool_vartable_t *table) {
  table->nvars = 1;
  reset_bgate_array(&table->gates);
  reset_ordata_array(&table->ordata);
  reset_clause_set(&table->clauses);
  reset_equiv_queue(&table->queue);
  reset_int_htbl(&table->htbl);
}


/*
 * Allocate a new variable index x
 * - set tag[x] to tag and desc[x] to index
 * - set root[x] to 1, and map[x] to null_literal
 */
static bvar_t bool_vartable_new_var(bool_vartable_t *table, uint8_t tag, uint32_t index) {
  uint32_t i;

  i = table->nvars;
  if (i == table->size) {
    extend_bool_vartable(table);
  }
  assert(i < table->size);

  table->tag[i] = tag;
  table->desc[i] = index;
  table->map[i] = null_literal;
  set_bit(table->root, i);

  table->nvars = i+1;

  return i;
}


/*
 * Add a clause a to the table
 * - n = number of literals
 */
void bool_vartable_add_clause(bool_vartable_t *table, uint32_t n, literal_t *a) {
  clause_set_add(&table->clauses, n, a);
}

void bool_vartable_add_empty_clause(bool_vartable_t *table) {
  clause_set_add_empty_clause(&table->clauses);
}

void bool_vartable_add_unit_clause(bool_vartable_t *table, literal_t l1) {
  clause_set_add_unit_clause(&table->clauses, l1);
}

void bool_vartable_add_binary_clause(bool_vartable_t *table, literal_t l1, literal_t l2) {
  clause_set_add_binary_clause(&table->clauses, l1, l2);
}

void bool_vartable_add_ternary_clause(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  clause_set_add_ternary_clause(&table->clauses, l1, l2, l3);
}



/*
 * Simplify then add clause a[0...n-1]
 *
 * Simplifications:
 * - sort, remove duplicates, remove false_literals, check for complementary or true literals
 */
void bool_vartable_simplify_and_add_clause(bool_vartable_t *table, uint32_t n, literal_t *a) {
  uint32_t i, p;
  literal_t l, aux;

  /*
   * First check for true literals and remove false literals
   */
  p = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    if (l == true_literal) return; // the clause is true
    if (l != false_literal) {
      a[p] = l;
      p ++;
    }
  }
  n = p;

  if (n == 0) {
    bool_vartable_add_empty_clause(table);
    return;
  }

  /*
   * Sort, remove duplicates, and check for complementary literals
   */
  int_array_sort(a, n);
  l = a[0];
  p = 1;
  for (i=1; i<n; i++) {
    aux = a[i];
    if (aux != l) {
      if (aux == not(l)) return; // true clause
      a[p] = aux;
      l = aux;
      p ++;
    }
  }

  bool_vartable_add_clause(table, p, a);
}


void bool_vartable_simplify_and_add_unit_clause(bool_vartable_t *table, literal_t l1) {
  bool_vartable_simplify_and_add_clause(table, 1, &l1);
}

void bool_vartable_simplify_and_add_binary_clause(bool_vartable_t *table, literal_t l1, literal_t l2) {
  literal_t aux[2];

  aux[0] = l1;
  aux[1] = l2;
  bool_vartable_simplify_and_add_clause(table, 2, aux);
}

void bool_vartable_simplify_and_add_ternary_clause(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  literal_t aux[3];

  aux[0] = l1;
  aux[1] = l2;
  aux[2] = l3;
  bool_vartable_simplify_and_add_clause(table, 3, aux);
}




/*
 * EQUIVALENCE CLASSES
 */

/*
 * Get the root literal in l's class
 */
literal_t literal_get_root(bool_vartable_t *table, literal_t l) {
  assert(valid_boolvar(table, var_of(l)));

  while (!tst_bit(table->root, var_of(l))) {
    // if l is pos(x), replace l by map[x]
    // if l is neg(x), replace l by not(map[x])
    assert(table->map[var_of(l)] != null_literal);
    l = table->map[var_of(l)] ^ sign_of_lit(l);
  }
  return l;
}


#ifndef NDEBUG
/*
 * Check whether the classes of l1 and l2 can be merged
 * - return true if l1 and l2 are in distinct/non-complementary classes,
 *   and if at least one of the two classes is not mapped to an external literal
 */
static bool root_literals_can_be_merged(bool_vartable_t *table, literal_t l1, literal_t l2) {
  bvar_t x1, x2;

  assert(literal_is_root(table, l1) && literal_is_root(table, l2));

  x1 = var_of(l1);
  x2 = var_of(l2);
  return x1 != x2 &&
    (root_boolvar_map(table, x1) == null_literal || root_boolvar_map(table, x2) == null_literal);
}
#endif


/*
 * Merge the classes of l1 and l2
 * - they must be in distinct and non-complementary classes
 */
static void merge_root_literals(bool_vartable_t *table, literal_t l1, literal_t l2) {
  literal_t aux;
  bvar_t x1;

  assert(root_literals_can_be_merged(table, l1, l2));

  if (table->map[var_of(l1)] != null_literal) {
    // swap l1 and l2
    aux = l1; l1 = l2; l2 = aux;
  }

  /*
   * If l1 is positive: store l2 in map[var_of(l1)]
   * If l1 is negative: store not(l2) in map[var_of(l1)]
   */
  x1 = var_of(l1);
  assert(table->map[x1] == null_literal);
  table->map[x1] = l2 ^ sign_of_lit(l1);
  clr_bit(table->root, x1);  // x1 is not a root anymore
}



/*
 * Add equality l1 == l2
 * - do nothing if this is a trivial equality
 * - add the empty clause if l1 == (not l2)
 * - otherwise, push [l1 == l2] into the internal queue
 *   then attempt to merge the classes of l1 and l2
 */
void  bool_vartable_push_eq(bool_vartable_t *table, literal_t l1, literal_t l2) {
  l1 = literal_get_root(table, l1);
  l2 = literal_get_root(table, l2);

  if (opposite(l1, l2)) {
    bool_vartable_add_empty_clause(table);
  } else if (l1 != l2) {
    if (l1 == true_literal)  { bool_vartable_add_unit_clause(table, l2); return; }
    if (l1 == false_literal) { bool_vartable_add_unit_clause(table, not(l2)); return; }
    if (l2 == true_literal)  { bool_vartable_add_unit_clause(table, l1); return; }
    if (l2 == false_literal) { bool_vartable_add_unit_clause(table, not(l1)); return; }

    push_equiv(&table->queue, l1, l2);
    if (root_boolvar_map(table, var_of(l1)) == null_literal ||
	root_boolvar_map(table, var_of(l2)) == null_literal) {
      merge_root_literals(table, l1, l2);
    }
  }
}


/*
 * VARIABLE CONSTRUCTORS
 */

/*
 * New variable (no definition)
 */
bvar_t make_fresh_boolvar(bool_vartable_t *table) {
  return bool_vartable_new_var(table, BVAR, 0);
}


/*
 * New atom with given tag and index
 */
bvar_t bool_vartable_add_atom(bool_vartable_t *table, uint8_t tag, uint32_t index) {
  assert(tag > BOR);
  return bool_vartable_new_var(table, tag, index);
}


/*
 * New gate
 */
static bvar_t bool_vartable_add_gate(bool_vartable_t *table, bgate_t *g) {
  uint32_t k;

  k = store_bgate(&table->gates, g);
  return bool_vartable_new_var(table, BGATE, k);
}


/*
 * New OR gate:
 * - n = arity
 * - a = array of n literals
 */
static bvar_t bool_vartable_add_or_gate(bool_vartable_t *table, uint32_t n, literal_t *a) {
  uint32_t k;

  k = store_ordata(&table->ordata, a, n);
  return bool_vartable_new_var(table, BOR, k);
}



/*
 * HASH CONSING
 */
typedef struct gate_hobj_s {
  int_hobj_t m;
  bool_vartable_t *table;
  bgate_t gate;
} gate_hobj_t;


typedef struct orgate_hobj_s {
  int_hobj_t m;
  bool_vartable_t *table;
  uint32_t n;
  literal_t *a;
} orgate_hobj_t;


static uint32_t hash_gate_hobj(gate_hobj_t *o) {
  return hash_bgate(&o->gate);
}

static uint32_t hash_orgate_hobj(orgate_hobj_t *o) {
  return hash_orgate(o->n, o->a);
}


static bool equal_gates(bgate_t *g1, bgate_t *g2) {
  return g1->ttbl == g2->ttbl && g1->var[0] == g2->var[0] &&
    g1->var[1] == g2->var[1] && g1->var[2] == g2->var[2];
}

static bool eq_gate_hobj(gate_hobj_t *o, int32_t i) {
  bool_vartable_t *table;

  table = o->table;
  return boolvar_is_gate(table, i) && equal_gates(&o->gate, boolvar_gate_desc(table, i));
}


static bool equal_or_gates(uint32_t n, literal_t *a, uint32_t *b) {
  uint32_t i;

  if (b[0] != n) return false;

  b ++;
  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return false;
  }

  return true;
}

static bool eq_orgate_hobj(orgate_hobj_t *o, int32_t i) {
  bool_vartable_t *table;

  table = o->table;
  return boolvar_is_or(table, i) && equal_or_gates(o->n, o->a, boolvar_or_desc(table, i));
}


static int32_t build_gate_hobj(gate_hobj_t *o) {
  return bool_vartable_add_gate(o->table, &o->gate);
}

static int32_t build_orgate_hobj(orgate_hobj_t *o) {
  return bool_vartable_add_or_gate(o->table, o->n, o->a);
}


/*
 * Hash-consing constructors
 */
static bvar_t get_bgate(bool_vartable_t *table, bgate_t *g) {
  gate_hobj_t gate_hobj;

  gate_hobj.m.hash = (hobj_hash_t) hash_gate_hobj;
  gate_hobj.m.eq = (hobj_eq_t) eq_gate_hobj;
  gate_hobj.m.build = (hobj_build_t) build_gate_hobj;
  gate_hobj.table = table;
  gate_hobj.gate = *g;
  return int_htbl_get_obj(&table->htbl, &gate_hobj.m);
}

static bvar_t get_bor(bool_vartable_t *table, uint32_t n, literal_t *a) {
  orgate_hobj_t orgate_hobj;

  orgate_hobj.m.hash = (hobj_hash_t) hash_orgate_hobj;
  orgate_hobj.m.eq = (hobj_eq_t) eq_orgate_hobj;
  orgate_hobj.m.build = (hobj_build_t) build_orgate_hobj;
  orgate_hobj.table = table;
  orgate_hobj.n = n;
  orgate_hobj.a = a;
  return int_htbl_get_obj(&table->htbl, &orgate_hobj.m);
}



/*
 * ELEMENTARY OPERATIONS ON TRUTH TABLES
 */

/*
 * We use the following operations to normalize a truth table:
 * - negate a column: if column i is labeled by (not x), then replace the
 *                    label by x and fix the bit mask (permutation)
 * - swap two adjacent columns
 * - remove irrelevant columns
 * - merge adjacent columns if they're labeled with the same variable
 * - remove column 0 if it's labeled with variable 0 (i.e., column 0 is the true constant)
 */


/*
 * negate column 0: input b7 b6 b5 b4 b3 b2 b1 b0
 *                 output b3 b2 b1 b0 b7 b6 b5 b4
 */
static inline uint8_t negate0(uint8_t b) {
  return (b & 0xf0) >> 4 | (b & 0x0f) << 4;
}

/*
 * negate column 1: input b7 b6 b5 b4 b3 b2 b1 b0
 *                 output b5 b4 b7 b6 b1 b0 b3 b2
 */
static inline uint8_t negate1(uint8_t b) {
  return (b & 0xcc) >> 2 | (b & 0x33) << 2;
}

/*
 * negate column 2: input b7 b6 b5 b4 b3 b2 b1 b0
 *                 output b6 b7 b4 b5 b2 b3 b0 b1
 */
static inline uint8_t negate2(uint8_t b) {
  return (b & 0xaa) >> 1 | (b & 0x55) << 1;
}

/*
 * swap columns 0 and 1: input b7 b6 b5 b4 b3 b2 b1 b0
 *                      output b7 b6 b3 b2 b5 b4 b1 b0
 */
static inline uint8_t swap01(uint8_t b) {
  return (b & 0xc3) | (b & 0x0c) << 2 | (b & 0x30) >> 2;
}

/*
 * swap columns 1 and 2: input b7 b6 b5 b4 b3 b2 b1 b0
 *                      output b7 b5 b6 b4 b3 b1 b2 b0
 */
static inline uint8_t swap12(uint8_t b) {
  return (b & 0x99) | (b & 0x22) << 1 | (b & 0x44) >> 1;
}

/*
 * remove column 0 (when true):
 *   input b7 b6 b5 b4 b3 b2 b1 b0
 *  output b7 b7 b6 b6 b5 b5 b4 b4
 */
static inline uint8_t force_true0(uint8_t b) {
  return (b & 0x80) | (b & 0xc0) >> 1 | (b & 0x60) >> 2 | (b & 0x30) >> 3 | (b & 0x10) >> 4;

}

/*
 * merge column 0 and 1 (equal labels)
 *   input b7 b6 b5 b4 b3 b2 b1 b0
 *  output b7 b7 b6 b6 b1 b1 b0 b0
 */
static inline uint8_t merge01(uint8_t b) {
  return (b & 0x81) | (b & 0xc0) >> 1 | (b & 0x40) >> 2 | (b & 0x02) << 2 | (b & 0x03) << 1;
}

/*
 * merge column 1 and 2 (equal labels)
 *   input: b7 b6 b5 b4 b3 b2 b1 b0
 *  output: b7 b7 b4 b4 b3 b3 b0 b0
 */
static inline uint8_t merge12(uint8_t b) {
  return (b & 0x99) | (b & 0x88) >> 1 | (b & 0x11) << 1;
}

/*
 * Check whether column 0 is irrelevant
 * - i.e. whether (b7 b6 b5 b4) == (b3 b2 b1 b0)
 */
static inline bool irrelevant0(uint8_t b) {
  return (b & 0x0f) == (b >> 4);
}

/*
 * Check whether column 1 is irrelevant (i.e., (b5 b4 b1 b0) == (b7 b6 b3 b2)
 */
static inline bool irrelevant1(uint8_t b) {
  return (b & 0x33) == (b & 0xcc) >> 2;
}

/*
 * Check whether column 2 is irrelevant (i.e., (b7 b5 b3 b1) == (b6 b4 b2 b0)
 */
static inline bool irrelevant2(uint8_t b) {
  return (b & 0x55) == (b & 0xaa) >> 1;
}


/*
 * Remove irrelevant columns
 */
// input: b3 b2 b1 b0 b3 b2 b1 b0 --> b3 b3 b2 b2 b1 b1 b0 b0
static inline uint8_t remove0(uint8_t b) {
  assert(irrelevant0(b));
  return (b & 0x81) | (b & 0xc0) >> 1 | (b & 0x60) >> 2 | (b & 0x03) << 1;
}

// input b3 b2 b3 b2 b1 b0 b1 b0 --> b3 b3 b2 b2 b1 b1 b0 b0
static inline uint8_t remove1(uint8_t b) {
  assert(irrelevant1(b));
  return (b & 0x99) | (b & 0x22) << 1 | (b & 0x44) >> 1;
}

// input: b3 b3 b2 b2 b1 b1 b0 b0 --> no change
static inline uint8_t remove2(uint8_t b) {
  assert(irrelevant2(b));
  return b;
}


/*
 * For debugging: check that tt is normalized
 */
#ifndef NDEBUG
static bool normal_truth_table(ttbl_t *tt) {
  switch (tt->nvars) {
  case 0:
    return tt->label[0] == null_bvar && tt->label[1] == null_bvar &&
      tt->label[2] == null_bvar && (tt->mask == 0x00 || tt->mask == 0xff);

  case 1:
    return tt->label[0] > const_bvar && tt->label[1] == null_bvar &&
      tt->label[2] == null_bvar && (tt->mask == 0xf0 || tt->mask == 0x0f);

  case 2:
    return tt->label[0] > const_bvar && tt->label[1] > tt->label[0] &&
      tt->label[2] == null_bvar && !irrelevant0(tt->mask) &&
      !irrelevant1(tt->mask) && irrelevant2(tt->mask);

  case 3:
    return tt->label[0] > const_bvar && tt->label[1] > tt->label[0] &&
      tt->label[2] > tt->label[1] && !irrelevant0(tt->mask) &&
      !irrelevant1(tt->mask) && !irrelevant2(tt->mask);

  default:
    return false;
  }
}

#endif


/*
 * Normalize truth table tt with three columns
 * - the three labels are literals
 */
static void normalize_truth_table3(ttbl_t *tt) {
  literal_t l;
  bvar_t aux;

  assert(tt->nvars == 3);

  // convert literals to variables and negate if required
  l = tt->label[0];
  tt->label[0] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate0(tt->mask);
  }

  l = tt->label[1];
  tt->label[1] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate1(tt->mask);
  }

  l = tt->label[2];
  tt->label[2] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate2(tt->mask);
  }

  // sort columns in non-decreasing order
  if (tt->label[0] > tt->label[1]) {
    aux = tt->label[0];
    tt->label[0] = tt->label[1];
    tt->label[1] = aux;
    tt->mask = swap01(tt->mask);
  }

  if (tt->label[1] > tt->label[2]) {
    aux = tt->label[1];
    tt->label[1] = tt->label[2];
    tt->label[2] = aux;
    tt->mask = swap12(tt->mask);
  }

  if (tt->label[0] > tt->label[1]) {
    aux = tt->label[0];
    tt->label[0] = tt->label[1];
    tt->label[1] = aux;
    tt->mask = swap01(tt->mask);
  }

  assert(0 <= tt->label[0] && tt->label[0] <= tt->label[1] && tt->label[1] <= tt->label[2]);

  // merge equal columns
  if (tt->label[1] == tt->label[2]) {
    tt->nvars --;
    tt->label[2] = null_bvar;
    tt->mask = merge12(tt->mask);
  }

  if (tt->label[0] == tt->label[1]) {
    tt->nvars --;
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = merge01(tt->mask);
  }

  // remove column 0 if it's true
  if (tt->label[0] == const_bvar) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = force_true0(tt->mask);
  }

  // remove irrelevant columns
  if (tt->nvars == 3 && irrelevant2(tt->mask)) {
    tt->nvars --;
    tt->label[2] = null_bvar;
    tt->mask = remove2(tt->mask);
  }

  if (tt->nvars > 1 && irrelevant1(tt->mask)) {
    tt->nvars --;
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = remove1(tt->mask);
  }

  if (tt->nvars > 0 && irrelevant0(tt->mask)) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = tt->label[2];
    tt->label[2] = null_bvar;
    tt->mask = remove0(tt->mask);
  }

}


/*
 * Normalize a truth table with two columns
 * - label[0] and label[1] are literals
 */
static void normalize_truth_table2(ttbl_t *tt) {
  literal_t l;
  bvar_t aux;

  assert(tt->nvars == 2 && tt->label[2] == null_bvar && irrelevant2(tt->mask));

  // convert literals to variables and negate if required
  l = tt->label[0];
  tt->label[0] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate0(tt->mask);
  }

  l = tt->label[1];
  tt->label[1] = var_of(l);
  if (is_neg(l)) {
    tt->mask = negate1(tt->mask);
  }

  // sort
  if (tt->label[0] > tt->label[1]) {
    aux = tt->label[0];
    tt->label[0] = tt->label[1];
    tt->label[1] = aux;
    tt->mask = swap01(tt->mask);
  }

  assert(0 <= tt->label[0] && tt->label[0] <= tt->label[1]);

  // merge columns if equal
  if (tt->label[0] == tt->label[1]) {
    tt->nvars --;
    tt->label[1] = null_bvar;
    tt->mask = merge01(tt->mask);
  }

  // remove column 0 if it's true
  if (tt->label[0] == const_bvar) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = null_bvar;
    tt->mask = force_true0(tt->mask);
  }

  // remove irrelevant columns
  if (tt->nvars == 2 && irrelevant1(tt->mask)) {
    tt->nvars --;
    tt->label[1] = null_bvar;
    tt->mask = remove1(tt->mask); // no change
  }

  if (tt->nvars > 0 && irrelevant0(tt->mask)) {
    tt->nvars --;
    tt->label[0] = tt->label[1];
    tt->label[1] = null_bvar;
    tt->mask = remove0(tt->mask);
  }

}



/*
 * When defining literal for a truth-table b, we have the choice between
 * - building variable v for gate b and return pos_lit(v)
 * - or building variable v for gate (~b) and return neg_lit(v)
 * To decide:
 * - we pick gate(b) if b has more '1' bits than ~b
 * - we pick gate(~b) if b has fewer '1' bits than ~b
 * - if b and ~b both have 4 bits equal to '1', we pick the
 *   one that has the lower order bit equal to '0'
 *
 * NOTE: these rules must be consistent with direct_or3, direct_or2
 * and direct_xor2.
 *
 * The following function returns true if ~b should be picked
 */
static inline bool negate_mask(uint8_t b) {
  uint32_t n1;

  n1 = popcount32(b);
  assert(0 <= n1 && n1 <= 8);
  return n1 < 4 || (n1 == 4 && ((b & 1) == 1));
}



/*
 * Return l == the function defined by tt
 * - tt must be normalized
 */
static literal_t gate_for_truth_table(bool_vartable_t *table, ttbl_t *tt) {
  bgate_t g;
  literal_t l;

  assert(normal_truth_table(tt));

  if (tt->nvars == 0) {
    assert(tt->mask == 0x00 || tt->mask == 0xff);
    l = true_literal;
    if (tt->mask == 0x00) {
      l = false_literal;
    }
  } else if (tt->nvars == 1) {
    assert(tt->mask == 0x0f || tt->mask == 0xf0);
    l = pos_lit(tt->label[0]);
    if (tt->mask == 0x0f) {
      l = not(l);
    }
  } else {
    assert(tt->nvars == 2 || tt->nvars == 3);
    g.var[0] = tt->label[0];
    g.var[1] = tt->label[1];
    g.var[2] = tt->label[2];
    if (negate_mask(tt->mask)) {
      g.ttbl = ~tt->mask;
      l = neg_lit(get_bgate(table, &g));
    } else {
      g.ttbl = tt->mask;
      l = pos_lit(get_bgate(table, &g));
    }
  }

  return l;
}


/*
 * Simplify then build l = (op l1 l2 l3)
 *  - op is defined by the bit mask b
 */
literal_t make_gate3(bool_vartable_t *table, uint8_t b, literal_t l1, literal_t l2, literal_t l3) {
  ttbl_t aux;

  assert(valid_literal(table, l1) && valid_literal(table, l2) && valid_literal(table, l3));

  aux.nvars = 3;
  aux.label[0] = l1;
  aux.label[1] = l2;
  aux.label[2] = l3;
  aux.mask = b;
  normalize_truth_table3(&aux);

  return gate_for_truth_table(table, &aux);
}


/*
 * Same thing for a binary operation
 */
literal_t make_gate2(bool_vartable_t *table, uint8_t b, literal_t l1, literal_t l2) {
  ttbl_t aux;

  assert(valid_literal(table, l1) && valid_literal(table, l2));

  aux.nvars = 2;
  aux.label[0] = l1;
  aux.label[1] = l2;
  aux.label[2] = null_bvar;
  aux.mask = b;
  normalize_truth_table2(&aux);

  return gate_for_truth_table(table, &aux);
}



/*
 * OR AND XOR GATES
 */

/*
 * Direct constructor for or gates
 * - no attempt to simplify
 */
static bvar_t direct_or2_gate(bool_vartable_t *table, literal_t l1, literal_t l2) {
  bgate_t g;
  uint8_t m1, m2;

  assert(false_literal < l1 && l1 < l2 && l1 != not(l2));

  m1 = 0xf0;
  if (is_neg(l1)) m1 = 0x0f;
  m2 = 0xcc;
  if (is_neg(l2)) m2 = 0x33;

  g.ttbl = (m1 | m2);
  g.var[0] = var_of(l1);
  g.var[1] = var_of(l2);
  g.var[2] = null_bvar;

  return get_bgate(table, &g);
}

static bvar_t direct_or3_gate(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  bgate_t g;
  uint8_t m1, m2, m3;

  assert(false_literal < l1 && l1 < l2 && l2 < l3 && l1 != not(l2) && l2 != not(l3));

  m1 = 0xf0;
  if (is_neg(l1)) m1 = 0x0f;
  m2 = 0xcc;
  if (is_neg(l2)) m2 = 0x33;
  m3 = 0xaa;
  if (is_neg(l3)) m3 = 0x55;

  g.ttbl = (m1 | m2 | m3);
  g.var[0] = var_of(l1);
  g.var[1] = var_of(l2);
  g.var[2] = var_of(l3);

  return get_bgate(table, &g);
}



/*
 * Same thing for binary xor
 */
static bvar_t direct_xor2_gate(bool_vartable_t *table, literal_t l1, literal_t l2) {
  bgate_t g;

  assert(is_pos(l1) && is_pos(l2) && l1 < l2 && false_literal < l1);

  g.ttbl = 0x3c;
  g.var[0] = var_of(l1);
  g.var[1] = var_of(l2);
  g.var[2] = null_bvar;

  return get_bgate(table, &g);
}



/*
 * Simplify and normalize (or a[0] ... a[n-1]) then build the gate
 * - assume that none of a[0] ... a[n-1] is true or false
 */
static literal_t make_or_aux(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t aux, l;
  uint32_t i, p;

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
      if (aux == not(l)) return true_literal;
      a[p] = aux;
      l = aux;
      p ++;
    }
  }

  // result: a[0 ... p-1]
  switch (p) {
  case 1:  return a[0];
  case 2:  return pos_lit(direct_or2_gate(table, a[0], a[1]));
  case 3:  return pos_lit(direct_or3_gate(table, a[0], a[1], a[2]));
  default: return pos_lit(get_bor(table, p, a));
  }
}




/*
 * Exported constructors for OR and AND
 */
literal_t make_or(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t l;
  uint32_t i, p;

  p = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    if (l == true_literal) return true_literal;
    if (l != false_literal) {
      a[p] = l;
      p ++;
    }
  }

  return make_or_aux(table, p, a);
}

literal_t make_and(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t l;
  uint32_t i, p;

  p = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    if (l == false_literal) return false_literal;
    if (l != true_literal) {
      a[p] = not(l);
      p ++;
    }
  }

  return not(make_or_aux(table, p, a));
}


/*
 * N-ary XOR constructor
 */
literal_t make_xor(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t l;
  uint32_t i, p, sign;

  /*
   * First pass: remove the true and false literals from a.
   * Convert all literals to positive polarity
   * Flip sign every time we flip a literal polarity
   */
  sign = 0;
  p = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    if (l == true_literal) {
      sign ^= 1; // flip sign
    } else if (l != false_literal) {
      sign ^= sign_of_lit(l);      // flip sign if l is negative
      a[p] = unsigned_literal(l);  // convert l to not(l) if l is negative
      p ++;
    }
  }
  n = p;


  /*
   * Second pass: sort then apply the rule (xor x x) = 0
   */
  if (n >= 2) {
    int_array_sort(a, n);
    p = 0;
    i = 0;
    while (i<n-1) {
      l = a[i];
      if (l == a[i+1]) {
        i += 2;
      } else {
        a[p] = l;
        p ++;
        i ++;
      }
    }
    assert(i == n-1 || i == n);
    if (i < n) {
      a[p] = a[i];
      p ++;
    }
    n = p;
  }


  /*
   * Result:  (xor a[0] ... a[n-1]) if sign is 0
   *      or (not (xor a[0] ... a[n-1])) if sign is 1
   */
  l = false_literal;
  if (n > 0) {
    l = a[0];
    for (i=1; i<n; i++) {
      l = pos_lit(direct_xor2_gate(table, l, a[i]));
    }
  }

  return l ^ sign;
}
