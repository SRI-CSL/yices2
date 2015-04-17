/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VARIABLE TABLE FOR DIFFERENCE LOGIC SOLVERS
 */

/*
 * Difference-logic solvers use Graph algorithms:
 * - vertices in the graph correspond to variables
 * - edges encode constraints of the form (x - y <= c)
 *
 * With the new context and new term representation, arithmetic atoms
 * are of the form (t == 0) or (t >= 0) or (t == u) where t and u are
 * arithmetic variables. For the difference logic fragments, we must
 * convert these terms to the form (x - y <= c) or (x - y == c) that
 * the graph algorithms can use. For this purpose, we store a mapping
 * from arithmetic variables to triples of the form
 *    [target vertex, source vertex, rational constant].
 * The triple [x, y, c] denotes the polynomial (x - y + c).
 */

#ifndef __DL_VARTABLE_H
#define __DL_VARTABLE_H

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#include "solvers/egraph/egraph_base_types.h"
#include "terms/poly_buffer.h"
#include "terms/rationals.h"
#include "utils/int_hash_tables.h"


/*
 * Each arithmetic variable is mapped internally to a triple
 * (constant, x, y), where x and y are either nil (-1) or vertices in
 * the difference logic graph.
 *
 * The triple is interpreted as the term (c + x - y):
 *   (c, nil, nil) --> c
 *   (c, x,   nil) --> c + x
 *   (c, nil, y)   --> c - y
 *   (c, x,   y)   --> c + x - y (with x != y)
 *
 * So (c + x - y) >= 0 <--> (y - x <= c) corresponds to adding
 * vertex of y ---> x of cost c in the solver graph.
 */
typedef struct dl_triple_s {
  int32_t target;      // variable x
  int32_t source;      // variable y
  rational_t constant; // constant c
} dl_triple_t;


/*
 * Marker: nil
 */
enum {
  nil_vertex = -1,
};


/*
 * Stack for push/pop:
 * - top = the current level (should be equal to base_level in the context)
 *   for 0 <= i < top: data[i] = number of variables defined at level i
 * - size = size of array data
 */
typedef struct dl_trail_stack_s {
  uint32_t size;
  uint32_t top;
  uint32_t *data;
} dl_trail_stack_t;

#define DEF_DL_TRAIL_SIZE 20
#define MAX_DL_TRAIL_SIZE (UINT32_MAX/sizeof(uint32_t))



/*
 * Variable table:
 * - nvars = number of variables in the table
 * - table->triple[i] = triple for variable x
 * - size = full size of array triple
 * - hash table for hash consing
 * - stack for push/pop
 */
typedef struct dl_vartable_s {
  uint32_t nvars;
  uint32_t size;
  dl_triple_t *triple;

  int_htbl_t htbl;
  dl_trail_stack_t stack;
} dl_vartable_t;


/*
 * Default and maximal size
 */
#define DEF_DL_VARTABLE_SIZE 100
#define MAX_DL_VARTABLE_SIZE (UINT32_MAX/sizeof(dl_triple_t))



/*
 * OPERATIONS ON VARIABLE TABLE
 */

/*
 * Initialization: use default sizes
 * - the table is empty
 */
extern void init_dl_vartable(dl_vartable_t *table);


/*
 * Delete: free memory
 */
extern void delete_dl_vartable(dl_vartable_t *table);


/*
 * Reset: clear the mapping/remove all variables
 */
extern void reset_dl_vartable(dl_vartable_t *table);


/*
 * Push: save the current number of variables
 */
extern void dl_vartable_push(dl_vartable_t *table);


/*
 * Pop: remove all variables created since the matching push
 * - the internal stack must not be empty
 */
extern void dl_vartable_pop(dl_vartable_t *table);


/*
 * Read the number of variables
 */
static inline uint32_t num_dl_vars(dl_vartable_t *table) {
  return table->nvars;
}


/*
 * VARIABLE CREATION/TRIPLE OPERATIONS
 */

/*
 * Get the descriptor of variable x:
 * WARNING: don't add stuff to the table as long as this pointer is in use.
 */
static inline dl_triple_t *dl_var_triple(dl_vartable_t *table, thvar_t x) {
  assert(0 <= x && x < table->nvars);
  return table->triple + x;
}


/*
 * Safer version: make a copy of the descriptor in d
 * - d->constant must be initialized
 */
extern void copy_dl_var_triple(dl_vartable_t *table, thvar_t x, dl_triple_t *d);


/*
 * Get a variable whose descriptor is equal to triple d
 * - return an existing variable if possible
 * - create a fresh variable with the given triple as descriptor otherwise
 */
extern thvar_t get_dl_var(dl_vartable_t *table, dl_triple_t *d);


/*
 * Add the triples for x and y and store the result in d
 * - return true if the result can be computed (i.e.,
 *   if triple(x) + triple(y) is of the form (w - z + c)
 * - return false otherwise.
 * - d->constant must be initialized
 */
extern bool sum_dl_vars(dl_vartable_t *table, thvar_t x, thvar_t y, dl_triple_t *d);


/*
 * Compute triple(x) - triple(y) and store the result in d if that's a triple
 * - return true if triple(x) - triple(y) is of the from (w - z + c)
 * - return false otherwise
 * - d->constant must be initialized
 */
extern bool diff_dl_vars(dl_vartable_t *table, thvar_t x, thvar_t y, dl_triple_t *d);




/*
 * POLYNOMIAL BUFFERS
 */

/*
 * When converting between difference logic triples and polynomials,
 * we shift all variable id by +1 or -1. In triples, target/source
 * are vertex indices in a graph. Vertices can be indexed from 0 to ..
 * In polynomials, variable index 0 is reserved for the constant term.
 *
 * The translation from vertex id to polynomial variable is then given by
 * - polynomial variable for vertex i is i+1
 * - vertex id for variable x is defined only if x>0 and it's equal to x-1
 *
 * All the following operations use this convention.
 */

/*
 * Operation between a poly buffer and a triple:
 * - add_dl_var_to_buffer:       add triple(x) to b
 * - sub_dl_var_from_buffer:     subtract triple(x) from b
 * - addmul_dl_var_to_buffer:    add a * triple(x) to b
 * - submul_dl_var_from_biuffer: subtract a * triple(x) from b
 * These operation do not normalize the buffer b
 */
extern void add_dl_var_to_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x);
extern void sub_dl_var_from_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x);
extern void addmul_dl_var_to_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x, rational_t *a);
extern void submul_dl_var_from_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x, rational_t *a);


/*
 * Check whether b is a triple (x - y + c) and store the result in d if so
 * - b must be normalized
 * - d->constant must be initialized
 * - return true if the conversion works
 * - return false otherwise
 */
extern bool convert_poly_buffer_to_dl_triple(poly_buffer_t *b, dl_triple_t *d);

/*
 * Try to convert poly buffer *b to a triple [x, y, c].
 * - if the conversion works, the returned triple satisfies the property
 *    (b >= 0) <==> (x - y + c >= 0)
 *   (i.e., the coefficients in b are divided by a positive constant).
 * - b must be normalized.
 * - d->constant must be initialized.
 * - return true if the conversion works and store the result into d.
 * - return false otherwise.
 */
extern bool rescale_poly_buffer_to_dl_triple(poly_buffer_t *b, dl_triple_t *d);


#endif /* __DL_VARTABLE_H */
