/*
 * Internalization table: maps integer indices to integers
 * - support reset/push/pop
 * - intended to support mapping of terms, arithmetic variables, and 
 *   bitvector variables to their internal representation (in core, 
 *   egraph, and theory solvers).
 */ 

#ifndef __INTERNALIZATION_MAP_H
#define __INTERNALIZATION_MAP_H

#include <assert.h>
#include <stdint.h>

#include "bitvectors.h"


/*
 * Trail stack:
 * - stack of integer values organized in frames
 * - a new frame is created by push
 * - pop removes the top frame
 * Fields:
 * - data = array to store the frames
 * - size = size of data array
 * - top = top of the stack
 * - top_frame = start of the top frame
 * - if top_frame = k then
 *   - k < top
 *   - the top frame is stored in data[k+1 .... top-1]
 *   - data[k] = index of the previous frame (saved value of top_frame)
 */
typedef struct itrail_s {
  uint32_t size;
  uint32_t top;
  int32_t top_frame;
  int32_t *data;
} itrail_t;


#define DEFAULT_ITRAIL_SIZE 20
#define MAX_ITRAIL_SIZE (UINT32_MAX>>2)


/*
 * Internalization table: maps int32 to int32
 * - data: stores the mapping
 * - size = size of the array data
 * - level = base_level = number of calls to push
 * - trail is initially NULL. A trail stack object is allocated
 *   on the first call to push.
 * - saved is a bit vector: if saved[x] = 1 then x is on the trail stack,
 *   in the top frame (to avoid saving x twice) 
 */
typedef struct itable_s {
  uint32_t size;
  uint32_t level;
  int32_t *data;
  itrail_t *trail;
  byte_t *saved;
} itable_t;


#define DEFAULT_ITABLE_SIZE 100
#define MAX_ITABLE_SIZE (UINT32_MAX>>2)


/*
 * Special code: nil = -1, mark = -2
 * - nil is used as initial value for data[i]
 * - mark is used to avoid visiting terms many times
 *
 * For DFS/cycle detection we mark terms white, grey, or black 
 * - white = nil (term not visited)
 * - grey = -3   (term found via DFS/not fully examined yet)
 * - black = -2  (fully explored)
 */
enum {
  nil = -1,
  mark = -2,

  white = -1,
  black = -2,
  grey = -3,
};




/****************
 *  OPERATIONS  *
 ***************/

/*
 * Initialize an internalization table
 * - n = initial size. 
 * - if n == 0, the default size is used.
 */
extern void init_itable(itable_t *table, uint32_t n);


/*
 * Delete: free all memory
 */
extern void delete_itable(itable_t *table);


/*
 * Reset: empty the table
 */
extern void reset_itable(itable_t *table);


/*
 * Push: start a new frame
 */
extern void itable_push(itable_t *table);


/*
 * Pop: remove all mappings added since the previous push. 
 */
extern void itable_pop(itable_t *table);


/*
 * Get value mapped to integer x
 * - return nil if nothing is mapped to x
 *   (including if x is >= table->size)
 * - x must be non-negative
 */
extern int32_t itable_get(itable_t *table, int32_t x);

/*
 * Add mapping [x --> k]
 * - x and k must be non-negative.
 * - x must not be mapped to anything
 * If push has been called, x is saved on the trail stack,
 * so that the mapping gets cleared by pop.
 */
extern void itable_map(itable_t *table, int32_t x, int32_t k);


/*
 * Overwrite the current mapping for x by k
 * - x must be mapped to something non-nil
 * The previous mapping is saved if necessary so that
 * it can be restored by pop.
 */
extern void itable_remap(itable_t *table, int32_t x, int32_t k);


/*
 * Get the number of elements in the mapping 
 * - this returns (x+1) where x is the last element with a non-nil value
 */
extern uint32_t itable_num_elements(itable_t *table);




/*
 * Markings: a mark is a negative value other than nil (or white).
 * Marks are intended to help detect cycles and mark visited terms
 * during internalization.
 */

/*
 * Auxiliary function: set k as a mark for x
 * - x must be non-negative and not mapped to anything
 * - k must be negative and non-nil
 */
extern void itable_set_mark(itable_t *table, int32_t x, int32_t k);


/*
 * Set a mark or color for x
 */
static inline void itable_mark(itable_t *table, int32_t x) {
  itable_set_mark(table, x, mark);
}

static inline void itable_mark_grey(itable_t *table, int32_t x) {
  itable_set_mark(table, x, grey);
}

static inline void itable_mark_black(itable_t *table, int32_t x) {
  itable_set_mark(table, x, black);
}


/*
 * Check the color
 */
static inline bool itable_is_white(itable_t *table, int32_t x) {
  return itable_get(table, x) == white;
}

static inline bool itable_is_grey(itable_t *table, int32_t x) {
  return itable_get(table, x) == grey;
}

static inline bool itable_is_black(itable_t *table, int32_t x) {
  return itable_get(table, x) == black;
}



/*
 * Remove the mark or reset x's color to white.
 */
static inline void itable_clr_mark(itable_t *table, int32_t x) {
  assert(0 <= x && x < table->size);
  table->data[x] = white;
}




#endif /* __INTERNALIZATION_MAP_H */
