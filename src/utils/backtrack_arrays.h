/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ARRAYS OF INTEGERS WITH SUPPORT FOR PUSH/POP
 * - each array stores a mapping from int32_t indices to an integer type.
 * - for now, the range can be: int32_t or uint8_t.
 */

#ifndef __BACKTRACK_ARRAYS_H
#define __BACKTRACK_ARRAYS_H

#include <stdint.h>
#include <assert.h>


/*
 * Undo stack: to revert the write operations
 * - elements in the undo stack are pairs (index, saved value)
 */
typedef struct array_undo_s {
  int32_t index;
  union {
    int32_t i32;
    uint8_t u8;
  } saved;
} array_undo_t;

typedef struct array_undo_stack_s {
  uint32_t size;
  uint32_t top;
  array_undo_t *data;
} array_undo_stack_t;


#define DEF_ARRAY_UNDO_SIZE 100
#define MAX_ARRAY_UNDO_SIZE (UINT32_MAX/sizeof(array_undo_stack_t))


/*
 * Trail stack: for each level, we keep
 * - the top of the undo stack on entry to that level
 */
typedef struct array_trail_s {
  uint32_t size;
  uint32_t top;
  uint32_t *undo_top;
} array_trail_t;


#define DEF_ARRAY_TRAIL_SIZE 30
#define MAX_ARRAY_TRAIL_SIZE (UINT32_MAX/sizeof(uint32_t))



/*
 * ARRAYS OF 32bit ELEMENTS
 */

/*
 * Full array:
 * - the current array is defined by map[0 ... top] and def
 *   array[i] = map[i]  if 0 <= i < top
 *   array[i] = def if top <= i
 * - size is the total size of map (as allocated)
 * - invariant top <= size holds
 */
// range = 32bit integers
typedef struct int32_array_s {
  int32_t *map;
  int32_t def;
  uint32_t top;
  uint32_t size;
  array_undo_stack_t undo;
  array_trail_t trail;
} int32_array_t;


#define DEF_INT32_ARRAY_SIZE 100
#define MAX_INT32_ARRAY_SIZE (UINT32_MAX/sizeof(int32_t))


/*
 * Initialize:
 * - def = default value
 * - n = initial size. If n=0, DEF_INT32_ARRAY_SIZE is used.
 * - the initial array maps everything to def
 */
extern void init_int32_array(int32_array_t *a, int32_t def, uint32_t n);


/*
 * Deletion
 */
extern void delete_int32_array(int32_array_t *a);


/*
 * Reset: to the initial array: a[i] = def for all i
 */
extern void reset_int32_array(int32_array_t *a);


/*
 * Push: start a new level. Mark a backtrack point.
 */
extern void int32_array_push(int32_array_t *a);


/*
 * Pop: restore the array to what it was on the matching 'push' operation.
 * - the trail stack must be non-empty.
 */
extern void int32_array_pop(int32_array_t *a);


/*
 * Store x in a[i].
 * - save the previous value of a[i] if necessary
 */
extern void ai32_write(int32_array_t *a, int32_t i, int32_t x);


/*
 * Read the current value at index i
 */
static inline int32_t ai32_read(int32_array_t *a, int32_t i) {
  assert(i >= 0);
  return (i < a->top) ? a->map[i] : a->def;
}


/*
 * Direct read: i must be between 0 and a->top
 */
static inline int32_t ai32_get(int32_array_t *a, int32_t i) {
  assert(0 <= i && i < a->top);
  return a->map[i];
}


/*
 * Direct write: i must be between 0 and a->top,
 * - this does not save the current value
 */
static inline void ai32_set(int32_array_t *a, int32_t i, int32_t x) {
  assert(0 <= i && i < a->top);
  a->map[i] = x;
}



/*
 * ARRAYS OF 8bit ELEMENTS
 */
typedef struct uint8_array_s {
  uint8_t *map;
  uint8_t def;
  uint32_t top;
  uint32_t size;
  array_undo_stack_t undo;
  array_trail_t trail;
} uint8_array_t;


#define DEF_UINT8_ARRAY_SIZE 100
#define MAX_UINT8_ARRAY_SIZE (UINT32_MAX/2)


/*
 * Initialize:
 * - def = default value
 * - n = initial size. If n=0, DEF_UINT8_ARRAY_SIZE is used.
 * - the initial array maps everything to def
 */
extern void init_uint8_array(uint8_array_t *a, uint8_t def, uint32_t n);


/*
 * Deletion
 */
extern void delete_uint8_array(uint8_array_t *a);


/*
 * Reset: to the initial array: a[i] = def for all i
 */
extern void reset_uint8_array(uint8_array_t *a);


/*
 * Push: start a new level. Mark a backtrack point.
 */
extern void uint8_array_push(uint8_array_t *a);


/*
 * Pop: restore the array to what it was on the matching 'push' operation.
 * - the trail stack must be non-empty.
 */
extern void uint8_array_pop(uint8_array_t *a);


/*
 * Store x in a[i].
 * - save the previous value of a[i] if necessary
 */
extern void au8_write(uint8_array_t *a, int32_t i, uint8_t x);


/*
 * Read the current value at index i
 */
static inline uint8_t au8_read(uint8_array_t *a, int32_t i) {
  assert(i >= 0);
  return (i < a->top) ? a->map[i] : a->def;
}


/*
 * Direct read: i must be between 0 and a->top
 */
static inline uint8_t au8_get(uint8_array_t *a, int32_t i) {
  assert(0 <= i && i < a->top);
  return a->map[i];
}

/*
 * Direct write: i must be between 0 and a->top
 * - the current value a->map[i] is not saved
 */
static inline void au8_set(uint8_array_t *a, int32_t i, uint8_t x) {
  assert(0 <= i && i < a->top);
  a->map[i] = x;
}



#endif /* __BACKTRACK_ARRAYS_H */
