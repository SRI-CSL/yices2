/*
 * TABLE OF BOOLEAN VARIABLES
 */

/*
 * Started 2012/05/08: the conversion of bit-vector constraints
 * to CNF is way too complicated, and not that good. This module
 * is intended to replace all that stuff.
 *
 * The conversion currently involve:
 * - bit_blaster
 * - remap_table
 * - gate_manager
 * - gate_hash_table
 *
 * The remap table attempts to keep track of equalities between
 * Boolean variables but it's imperfect. The gate manager and 
 * gate_hash_table keep track of gate definitions and are used
 * for hash-consing. 
 *
 * One issue: for each gate, we create clauses at the time the
 * Boolean gate is created. Also sometimes Boolean variables
 * are created and bypass the remap_table (i.e., x and y are
 * created and later we assert that they are equal).
 *
 * Overall, it makes more sense to keep track of equalities between
 * variables, and delay the conversion to CNF until all the gates have
 * been created, and all equalities have been processed.
 *
 * That's what this module is intendend for:
 * - it stores a set of Boolean variables. Each variable has 
 *   a descriptor (i.e., the variable definition).
 * - the definitions may be:
 *   1) a pure variable (i.e., no definition)
 *   2) a Boolean function of other variables
 *   3) a theory atom
 *
 * We support the following Boolean functions:
 *   (OR a_1 ... a_n)
 *   (XOR a_1 ... a_n)
 *   (ITE c a b) := (c => a) & (not c => b)
 *   (CMP a b c) := (a (not b) | a c | c (not b))
 *   (MAJ a b c) := (a b | a c | b c)
 *
 * (CMP a b c) is a 'one-bit' comparator with c as carry-in:
 *   (CMP a b c) := (a > b) or ((a = b) and c)
 *
 * (MAJ a b c) is the majority of a, b, c. It can be used to
 * build full adders. 
 *
 * NOTE: we have (CMP a b c) = (MAJ a (not b) c)
 *
 * The majority of functions used in bitvector problems have
 * two or three variables. We represent a function (f x y z) 
 * compactly using its truth table, which is stored as four integers:
 * - a bitmask for the truth table (8bits are used)
 * - the three variables x, y, z in increasing order
 */

#ifndef __BOOL_VARTABLE_H
#define __BOOL_VARTABLE_H

#include <stdint.h>
#include <stdbool.h>

#include "int_hash_tables.h"
#include "smt_core.h" 


/*
 * We use an 8bit tag for each variable:
 *   BCONST = Boolean constant (true) = variable 0
 *   BVAR = variable (no definition)
 *   BGATE = Boolean function of no more than 3 variables
 *   BOR = large or (more than 3 variables)
 * the other tags can be used for theory atoms
 */
enum {
  BCONST,
  BVAR,
  BGATE,
  BOR,
};


/*
 * Descriptor for a Boolean gate (function of arity <= 3)
 * - for functions of arity 3, 
 *     var[0], var[1], var[2] are the indices of three Boolean variables 
 *     in increasing order
 * - for functions of arity 2, var[2] is not used (it's null_bvar = -1)
 *     var[0] and var[1] are two Boolean variables
 *
 * - the truth table is an array of 8bits b7 ... b0
 * - the encoding is as follows
 *
 *    var[0] var[1] var[2]  f
 *       0      0      0    b0
 *       0      0      1    b1
 *       0      1      0    b2
 *       0      1      1    b3
 *       1      0      0    b4
 *       1      0      1    b5
 *       1      1      0    b6
 *       1      1      1    b7
 *
 * For functions of arity 2, this looks like:
 *
 *    var[0] var[1] var[2]  f
 *       0      0      0    b0
 *       0      0      1    b0
 *       0      1      0    b2
 *       0      1      1    b2
 *       1      0      0    b4
 *       1      0      1    b4
 *       1      1      0    b6
 *       1      1      1    b6
 *
 * and var[2] is set to -1.
 */
typedef struct bgate_s {
  uint8_t ttbl; // truth table
  bvar_t  var[3]; // variables in increasing order
} bgate_t;



/*
 * Intermediate structure to store a truth table:
 * - this is used during gate construction to simplify and normalize truth tables/
 * - a table consists of nvars columns where nvars is between 0 and 3
 * - each column is labeled by a signed integer, which can be either a literal
 *   or a Boolean variable, or -1
 * - the truth values are stored in a bit mask (8 bit, unsigned word).
 *   all 8bits are used even if the table has fewer than 3 columms.
 */
typedef struct ttbl_s {
  uint32_t nvars;     // number of columns (between 0 and 3)
  int32_t  label[3] ; // column labels
  uint8_t  mask;      // 8-bit truth table
} ttbl_t;



/*
 * Resizable array of bgate_t descriptors
 * - size = size of array data
 * - ngates = total number of gates in use
 */
typedef struct bgate_array_s {
  bgate_t *data;
  uint32_t ngates;
  uint32_t size;
} bgate_array_t;

#define DEF_BGATE_ARRAY_SIZE 1024
#define MAX_BGATE_ARRAY_SIZE (UINT32_MAX/sizeof(bgate_t))


/*
 * Resizable integer array used as descriptors of 
 * large OR gates.
 * - the descriptors are stored in data[0 .... top-1]
 * - if a descriptor starts at index k then
 *   data[k] = arity of the OR gate = n
 *   data[k+1, ..., k+n] = arguments (i.e., n literals)
 * - the next descriptor starts at index k+n+1
 */
typedef struct ordata_array_s {
  int32_t *data;
  uint32_t top;
  uint32_t size;  
} ordata_array_t;

#define DEF_ORDATA_ARRAY_SIZE 1000
#define MAX_ORDATA_ARRAY_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Variable table
 * - for each variable: 
 *   tag[x] = 8bit
 *   desc[x] = 32bit index
 * - if tag[x] = BCONST or tag[x] = BVAR then desc[x] is not used (it's set to 0)
 * - if tag[x] = BGATE then desc[x] = index k in the gate array
 * - if tag[x] = BOR then desc[x] = index k in array data
 */
typedef struct bool_vartable_s {
  uint32_t nvars;   // number of variables 
  uint32_t size;    // size of arrays tag and desc
  uint8_t *tag;
  uint32_t *desc;
  bgate_array_t gates;
  ordata_array_t ordata;

  int_htbl_t htbl;  // for hash consing
} bool_vartable_t;


#define DEF_BOOLVARTABLE_SIZE 1000
#define MAX_BOOLVARTABLE_SIZE (UINT32_MAX/sizeof(uint32_t))




/*
 * GLOBAL OPERATION
 */

/*
 * Initialize the table: this creates variable 0 = true
 */
extern void init_bool_vartable(bool_vartable_t *table);


/*
 * Free memory
 */
extern void delete_bool_vartable(bool_vartable_t *table);


/*
 * Reset: empty the table. All variables and descriptors are 
 * removed except variable 0.
 */
extern void reset_bool_vartable(bool_vartable_t *table);



/*
 * ACCESS TO DESCRIPTORS
 */
static inline bool valid_boolvar(bool_vartable_t *table, bvar_t x) {
  return 0 <= x  && x < table->nvars;
}

static inline bool valid_literal(bool_vartable_t *table, literal_t l) {
  return valid_boolvar(table, var_of(l));
}

static inline uint8_t boolvar_tag(bool_vartable_t *table, bvar_t x) {
  assert(valid_boolvar(table, x));
  return table->tag[x];
}

static inline uint32_t boolvar_index(bool_vartable_t *table, bvar_t x) {
  assert(valid_boolvar(table, x));
  return table->desc[x];
}

static inline bool boolvar_is_const(bool_vartable_t *table, bvar_t x) {
  return boolvar_tag(table, x) == BCONST;
}

static inline bool boolvar_is_var(bool_vartable_t *table, bvar_t x) {
  return boolvar_tag(table, x) == BVAR;
}

static inline bool boolvar_is_gate(bool_vartable_t *table, bvar_t x) {
  return boolvar_tag(table, x) == BGATE;
}

static inline bool boolvar_is_or(bool_vartable_t *table, bvar_t x) {
  return boolvar_tag(table, x) == BOR;
}

static inline bool boolvar_is_atom(bool_vartable_t *table, bvar_t x) {
  return boolvar_tag(table, x) > BOR;
}

static inline bgate_t *boolvar_gate_desc(bool_vartable_t *table, bvar_t x) {
  assert(boolvar_is_gate(table, x));
  return table->gates.data + table->desc[x];
}

static inline int32_t *boolvar_or_desc(bool_vartable_t *table, bvar_t x) {
  assert(boolvar_is_or(table, x));
  return table->ordata.data + table->desc[x];
}




/*
 * VARIABLE CONSTRUCTORS
 */

/*
 * New variable (no definition)
 */
extern bvar_t make_fresh_boolvar(bool_vartable_t *table);

static inline literal_t make_fresh_literal(bool_vartable_t *table) {
  return pos_lit(make_fresh_boolvar(table));
}


/*
 * Theory atom:
 * - tag = an identifier used by the theory solver (it must not be
 *   one of the four reserved tags above)
 * - index = an index also used by the theory solver
 * This function does not use hash-consing. It creates a fresh variable
 * index and returns it.
 */
extern bvar_t bool_vartable_add_atom(bool_vartable_t *table, uint8_t tag, uint32_t index);


/*
 * Gate constructors: the functions take two or three literals as input
 *   and return a literal
 * - each literal must be of the form pos_lit(x) or neg_lit(x)
 *   where x is a variable in the table.
 * - the actual gate is defined by the 8bit truth-table b
 * - for make_gate2, b must be of the form [b3 b3 b2 b2 b1 b1 b0 b0]
 */
extern literal_t make_gate3(bool_vartable_t *table, uint8_t b, literal_t l1, literal_t l2, literal_t l3);
extern literal_t make_gate2(bool_vartable_t *table, uint8_t b, literal_t l1, literal_t l2);



/*
 * Primitive gates
 */
static inline literal_t make_or2(bool_vartable_t *table, literal_t l1, literal_t l2) {
  return make_gate2(table, 0xfc, l1, l2);
}

static inline literal_t make_xor2(bool_vartable_t *table, literal_t l1, literal_t l2) {
  return make_gate2(table, 0x3c, l1, l2);
}

static inline literal_t make_or3(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  return make_gate3(table, 0xfe, l1, l2, l3);
}

static inline literal_t make_xor3(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  return make_gate3(table, 0x96, l1, l2, l3);
}

static inline literal_t make_maj3(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  return make_gate3(table, 0xe8, l1, l2, l3);
}

static inline literal_t make_ite(bool_vartable_t *table, literal_t c, literal_t l1, literal_t l2) {
  return make_gate3(table, 0xca, c, l1, l2);
}



/*
 * Derived gates
 */
static inline literal_t make_and2(bool_vartable_t *table, literal_t l1, literal_t l2) {
  return not(make_or2(table, not(l1), not(l2)));
}

static inline literal_t make_and3(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  return not(make_or3(table, not(l1), not(l2), not(l3)));
}

static inline literal_t make_implies(bool_vartable_t *table, literal_t l1, literal_t l2) {
  return make_or2(table, not(l1), l2);
}

static inline literal_t make_iff(bool_vartable_t *table, literal_t l1, literal_t l2) {
  return not(make_xor2(table, l1, l2));
}

static inline literal_t make_cmp(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  return make_maj3(table, l1, not(l2), l3);
}



/*
 * Large arity OR/AND/XOR gates
 * - n = arity
 * - a[0 ... n-1] = arguments
 * Warning: a may be modified
 */
extern literal_t make_or(bool_vartable_t *table, uint32_t n, literal_t *a);
extern literal_t make_and(bool_vartable_t *table, uint32_t n, literal_t *a);
extern literal_t make_xor(bool_vartable_t *table, uint32_t n, literal_t *a);



#endif /* __BOOL_VARTABLE_H */
