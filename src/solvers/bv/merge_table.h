/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MERGE TABLE: STORE EQUIVALENCE CLASSES OF VARIABLES
 */

#ifndef __MERGE_TABLE_H
#define __MERGE_TABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

/*
 * In the bitvector solver, variables get ultimately mapped to arrays
 * of (pseudo) literals. If two variables are asserted equal at the
 * base level, then we want to avoid allocating two arrays of
 * literals, and instead map both of them to the same literal array.
 *
 * To support this, we maintain an equivalence relation between
 * variables (two variables are in the same equivalence classes if
 * they are asserted equal at the base level). This is implemented
 * using a merge table. This is a simplified version of a union-find
 * data structure so that push/pop is cheap.
 *
 * The merge table maps a variable x to its parent in a merge tree.
 * - each variable x is a non-negative integer
 * - if map[x] is -1 then x is root of its class.
 * - for backtracking, we keeps an undo stack + trail stack
 *   as in remap_table and backtrack_arrays.
 */

/*
 * Undo stack: keeps track of indices x such that map[x] != null
 */
typedef struct mtbl_undo_stack_s {
  uint32_t size;
  uint32_t top;
  int32_t *data;
} mtbl_undo_stack_t;


#define DEF_MTBL_UNDO_SIZE 100
#define MAX_MTBL_UNDO_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Trail stack: for each level, keeps track of
 * - top of the undo stack
 * - top map = 1 + largest index x such that map[x] != null
 */
typedef struct mtbl_trail_elem_s {
  uint32_t map_top;
  uint32_t undo_top;
} mtbl_trail_elem_t;

typedef struct mtbl_trail_s {
  uint32_t size;
  uint32_t top;
  mtbl_trail_elem_t *data;
} mtbl_trail_t;

#define DEF_MTBL_TRAIL_SIZE 30
#define MAX_MTBL_TRAIL_SIZE (UINT32_MAX/sizeof(mtbl_trail_elem_t))


/*
 * Merge table:
 * - the current maps is defined by map[0 ... top - 1]
 * - for any non-negative x:
 *   parent[x] = map[x] if 0 <= x < top
 *   parent[x] = -1 otherwise
 * - prev_top = value of top on the preceding call to push
 *   (or 0 initially)
 *   when map[x] is written, we need to save x on the undo
 *   stack only if 0 <= x < prev_top.
 * - size = total size of the map array
 */
typedef struct mtbl_s {
  int32_t *map;
  uint32_t top;
  uint32_t prev_top;
  uint32_t size;
  mtbl_undo_stack_t undo;
  mtbl_trail_t trail;
} mtbl_t;


#define DEF_MTBL_MAP_SIZE 100
#define MAX_MTBL_MAP_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * OPERATIONS
 */

/*
 * Initialize table: all empty
 */
extern void init_mtbl(mtbl_t *table);


/*
 * Delete: free all memory used by table
 */
extern void delete_mtbl(mtbl_t *table);


/*
 * Reset: empty the table
 */
extern void reset_mtbl(mtbl_t *table);


/*
 * Push: start a new backtrack level
 */
extern void mtbl_push(mtbl_t *table);


/*
 * Pop: restore the table to what it was on the
 * matching push.
 * - the trail_stack must be non-empty
 */
extern void mtbl_pop(mtbl_t *table);


/*
 * Get the root of x in the merge table
 * - x must be non-negative
 * - return x itself if x >= mtbl->top
 */
extern int32_t mtbl_get_root(mtbl_t *table, int32_t x);


/*
 * Check whether x is a root
 * - x must be non-negative
 */
static inline bool mtbl_is_root(mtbl_t *table, int32_t x) {
  assert(x >= 0);
  return x >= table->top || table->map[x] < 0;
}


/*
 * Check whether x and y are in the same equivalence class
 * - both x and y must be non-negative
 */
extern bool mtbl_equiv(mtbl_t *table, int32_t x, int32_t y);


/*
 * Add the mapping parent[x] := y to the table
 * - both x and y must be non-negative
 * - x must be a root
 * - y must be different from x
 */
extern void mtbl_map(mtbl_t *table, int32_t x, int32_t y);


#endif /* __MERGE_TABLE_H */
