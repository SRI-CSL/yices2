/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH TABLE FOR BOOLEAN GATES
 */

/*
 * This provides support for encoding and hash-consing boolean combinators
 * (xor, or, and, iff, ite, etc.)
 * - Inputs and outputs of a gate are literals.
 * - Combinators may have several outputs (e.g., a single-bit adder)
 * - Push and pop operations are supported
 */

#ifndef __GATES_HASH_TABLE_H
#define __GATES_HASH_TABLE_H

#include <stdint.h>
#include <assert.h>

#include "solvers/cdcl/smt_core.h"


/*
 * Logical gates and building blocks for bit-vector arithmetic
 * -----------------------------------------------------------
 *
 * XOR(a_1, ..., a_n)(b)  b = (xor a_1 ... a_n)
 *
 *  OR(a_1, ..., a_n)(b)  b = (or a_1 ... a_n)
 *
 * ITE(c, a1, a2)(b)      b = (ite c a1 a2)
 *
 *
 * Building block for comparators:
 *
 * CMP(a1, a2, c)(b)     b = ((a1 > a2) or (a_1 == a2 and c))
 *
 * Adders:
 *
 * HALFADD(a1, a2)(s, c)      s = (xor a1 a2)
 *                            c = (a1 and a2)
 *
 * FULLADD(a1, a2, c)(s, d)   s = (xor a1 a2 c)
 *                            d = (or (and a1 a2) (and a1 c) (and a2 c))
 *
 */
typedef enum gate_op {
  XOR_GATE,
  OR_GATE,
  ITE_GATE,
  CMP_GATE,
  HALFADD_GATE,
  FULLADD_GATE,
} gate_op_t;

#define GTAG_NUM_OPS (FULLADD_GATE + 1)



/*
 * Gate descriptor:
 * - 32bit tag encodes operator + indegree + outdegree
 * - if indegree is k and outdegree is j, then
 *      lit[0 ... k-1] are the input literals
 *      lit[k ... k+j-1] are the output literals
 * - each descriptor also includes a hash code = hash of tag + input literals
 */


/*
 * Tag structure
 * - 8 bits for the operator (bits 24 to 31)
 * - 8 bits for outdegree (bits 16 to 23)
 * - 16 bits for indegree (bits 0 to 15)
 */
#define GTAG_OPCODE_BITS 8
#define GTAG_ODEG_BITS   8
#define GTAG_IDEG_BITS   16

#define MAX_OPCODE     ((1<<GTAG_OPCODE_BITS)-1)
#define MAX_OUTDEGREE  ((uint32_t)((1<<GTAG_ODEG_BITS)-1))
#define MAX_INDEGREE   ((uint32_t)((1<<GTAG_IDEG_BITS)-1))

#define GTAG_GATE_SHIFT (GTAG_IDEG_BITS+GTAG_ODEG_BITS)
#define GTAG_ODEG_SHIFT GTAG_IDEG_BITS

#define GTAG_ODEG_MASK  MAX_OUTDEGREE
#define GTAG_IDEG_MASK  MAX_INDEGREE


static inline gate_op_t tag_combinator(uint32_t tag) {
  return (gate_op_t) (tag >> GTAG_GATE_SHIFT);
}

static inline uint32_t tag_outdegree(uint32_t tag) {
  return (tag >> GTAG_ODEG_SHIFT) & GTAG_ODEG_MASK;
}

static inline uint32_t tag_indegree(uint32_t tag) {
  return tag & GTAG_IDEG_MASK;
}

// clang gives warning for op <= MAX_OPCODE: coerced op to int to fix that
static inline uint32_t mk_gate_tag(gate_op_t op, uint32_t in_deg, uint32_t out_deg) {
  assert((int) op <= MAX_OPCODE && in_deg <= MAX_INDEGREE && out_deg <= MAX_OUTDEGREE);
  return (((uint32_t)op) << GTAG_GATE_SHIFT) | (out_deg << GTAG_ODEG_SHIFT) | in_deg;
}

static inline uint32_t orgate_tag(uint32_t in_deg) {
  return mk_gate_tag(OR_GATE, in_deg, 1);
}

static inline uint32_t xorgate_tag(uint32_t in_deg) {
  return mk_gate_tag(XOR_GATE, in_deg, 1);
}

static inline uint32_t itegate_tag(void) {
  return mk_gate_tag(ITE_GATE, 3, 1);
}

static inline uint32_t cmpgate_tag(void) {
  return mk_gate_tag(CMP_GATE, 3, 1);
}

static inline uint32_t halfaddgate_tag(void) {
  return mk_gate_tag(HALFADD_GATE, 2, 2);
}

static inline uint32_t fulladdgate_tag(void) {
  return mk_gate_tag(FULLADD_GATE, 3, 2);
}



/*
 * Descriptor of a boolean gate
 */
typedef struct boolgate_s {
  uint32_t hash;
  uint32_t tag;
  literal_t lit[0]; // real size depends on tag
} boolgate_t;


/*
 * List of boolean gates (for pop operation)
 */
typedef struct lnkgate_s lnkgate_t;

struct lnkgate_s {
  lnkgate_t *next;
  boolgate_t gate;
};



/*
 * Stack of lists for push/pop
 * - objects created at level k>0 are stored in a linked list
 * - on exit from level k (pop operation), all elements
 *   created in that level must be removed.
 * - for push/pop, we maintain a stack of list descriptors;
 *   each descriptor is a pair <level, list> (i.e., the list
 *   of objects created at that level).
 * - the descriptors are in data[0 ... nlists-1] with
 *      data[i].level < data[i+1].level
 *      data[i].list is not empty
 *      data[i].level <= current_level
 * - top_level is 0 if the stack is empty
 *   otherwise top_level = data[nlist-1].level
 * - nlist = the top of the list
 * - size = size of the data array
 */
typedef struct levlist_s {
  uint32_t level;
  lnkgate_t *list;
} levlist_t;

typedef struct levlist_stack_s {
  uint32_t current_level;
  uint32_t top_level;
  uint32_t nlists;
  uint32_t size;
  levlist_t *data;
} levlist_stack_t;


#define DEF_LEVLIST_STACK_SIZE 10
#define MAX_LEVLIST_STACK_SIZE (UINT32_MAX/sizeof(levlist_t))



/*
 * Hash table (similar to int_hash_table, etc.).
 */
typedef struct gate_htbl_s {
  boolgate_t **data;  // hash table proper
  uint32_t size;      // its size (power of 2)
  uint32_t nelems;    // number of elements
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} gate_htbl_t;


/*
 * Marker for deleted elements in data array
 * - data[i] = NULL if it's empty
 */
#define DELETED_GATE ((boolgate_t*) 1)

#define DEF_GATE_HTBL_SIZE 32
#define MAX_GATE_HTBL_SIZE (UINT32_MAX/sizeof(boolgate_t*))
#define GATE_HTBL_RESIZE_RATIO  0.6
#define GATE_HTBL_CLEANUP_RATIO 0.2




/*
 * Full hash_consing structure
 */
typedef struct gate_table_s {
  levlist_stack_t stack;
  gate_htbl_t htbl;
} gate_table_t;




/***********************
 *  CREATION/DELETION  *
 **********************/

/*
 * Initialize table: memory for stack and hash-table is not
 * allocated yet.
 */
extern void init_gate_table(gate_table_t *table);

/*
 * Delete all objects stored in the table and all allocated memory
 */
extern void delete_gate_table(gate_table_t *table);

/*
 * Empty the table and set current_level to 0
 */
extern void reset_gate_table(gate_table_t *table);

/*
 * Push
 */
static inline void gate_table_push(gate_table_t *table) {
  table->stack.current_level ++;
}

/*
 * Pop: delete all objects created at the current level
 * then decrement current_level. Should not be called at level 0.
 */
extern void gate_table_pop(gate_table_t *table);


/*
 * Set level: same effect as calling push n times
 */
static inline void gate_table_set_level(gate_table_t *table, uint32_t n) {
  assert(table->stack.current_level == 0);
  table->stack.current_level = n;
}



/***************************
 *  HASH-TABLE OPERATIONS  *
 **************************/

/*
 * Find a descriptor with the given tag and input literals
 * - the input literals are in a[0 ... n-1] where n = indegree(tag)
 * - return NULL if there's no matching record in the table
 */
extern boolgate_t *gate_table_find(gate_table_t *table, uint32_t tag, literal_t *a);

/*
 * Find or create a descriptor with the given tag/input literals
 * - if the descriptor is new, then its output are initialized to null_literal
 */
extern boolgate_t *gate_table_get(gate_table_t *table, uint32_t tag, literal_t *a);


/*
 * Find and get for (op a b) and (op a b c)
 */
extern boolgate_t *gate_table_find2(gate_table_t *table, uint32_t tag, literal_t a, literal_t b);
extern boolgate_t *gate_table_get2(gate_table_t *table, uint32_t tag, literal_t a, literal_t b);
extern boolgate_t *gate_table_find3(gate_table_t *table, uint32_t tag, literal_t a, literal_t b, literal_t c);
extern boolgate_t *gate_table_get3(gate_table_t *table, uint32_t tag, literal_t a, literal_t b, literal_t c);


/*
 * Short cuts: (or a[0] ... a[n-1]) and (xor a[0] ... a[n-1])
 */
static inline boolgate_t *gate_table_find_or(gate_table_t *table, uint32_t n, literal_t *a) {
  return gate_table_find(table, orgate_tag(n), a);
}
static inline boolgate_t *gate_table_find_xor(gate_table_t *table, uint32_t n, literal_t *a) {
  return gate_table_find(table, xorgate_tag(n), a);
}

static inline boolgate_t *gate_table_get_or(gate_table_t *table, uint32_t n, literal_t *a) {
  return gate_table_get(table, orgate_tag(n), a);
}
static inline boolgate_t *gate_table_get_xor(gate_table_t *table, uint32_t n, literal_t *a) {
  return gate_table_get(table, xorgate_tag(n), a);
}


/*
 * All binary and ternary gates
 */
static inline boolgate_t *gate_table_find_or2(gate_table_t *table, literal_t a, literal_t b) {
  return gate_table_find2(table, orgate_tag(2), a, b);
}

static inline boolgate_t *gate_table_find_xor2(gate_table_t *table, literal_t a, literal_t b) {
  return gate_table_find2(table, xorgate_tag(2), a, b);
}

static inline boolgate_t *gate_table_find_halfadd(gate_table_t *table, literal_t a, literal_t b) {
  return gate_table_find2(table, halfaddgate_tag(), a, b);
}

static inline boolgate_t *gate_table_find_or3(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_find3(table, orgate_tag(3), a, b, c);
}

static inline boolgate_t *gate_table_find_xor3(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_find3(table, xorgate_tag(3), a, b, c);
}

static inline boolgate_t *gate_table_find_ite(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_find3(table, itegate_tag(), a, b, c);
}

static inline boolgate_t *gate_table_find_cmp(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_find3(table, cmpgate_tag(), a, b, c);
}

static inline boolgate_t *gate_table_find_fulladd(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_find3(table, fulladdgate_tag(), a, b, c);
}



/*
 * All binary and ternary gates
 */
static inline boolgate_t *gate_table_get_or2(gate_table_t *table, literal_t a, literal_t b) {
  return gate_table_get2(table, orgate_tag(2), a, b);
}

static inline boolgate_t *gate_table_get_xor2(gate_table_t *table, literal_t a, literal_t b) {
  return gate_table_get2(table, xorgate_tag(2), a, b);
}

static inline boolgate_t *gate_table_get_halfadd(gate_table_t *table, literal_t a, literal_t b) {
  return gate_table_get2(table, halfaddgate_tag(), a, b);
}

static inline boolgate_t *gate_table_get_or3(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_get3(table, orgate_tag(3), a, b, c);
}

static inline boolgate_t *gate_table_get_xor3(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_get3(table, xorgate_tag(3), a, b, c);
}

static inline boolgate_t *gate_table_get_ite(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_get3(table, itegate_tag(), a, b, c);
}

static inline boolgate_t *gate_table_get_cmp(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_get3(table, cmpgate_tag(), a, b, c);
}

static inline boolgate_t *gate_table_get_fulladd(gate_table_t *table, literal_t a, literal_t b, literal_t c) {
  return gate_table_get3(table, fulladdgate_tag(), a, b, c);
}





#endif /* __GATES_HASH_TABLE_H */
