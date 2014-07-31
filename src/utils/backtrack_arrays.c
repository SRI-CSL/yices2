/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ARRAYS OF INTEGERS WITH SUPPORT FOR PUSH/POP.
 * - each array stores a mapping from int32_t indices to an integer type.
 * - for now, the range can be: int32_t or uint8_t.
 */

#include <stdbool.h>

#include "utils/memalloc.h"
#include "utils/backtrack_arrays.h"


/*
 * UNDO STACK
 */

/*
 * Initialize: initial size = 0
 * - data is allocated on the first call to push
 */
static void init_array_undo_stack(array_undo_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}


/*
 * Make the stack larger
 * - allocate the initial array if size = 0
 * - make the array 50% larger otherwise
 */
static void extend_array_undo_stack(array_undo_stack_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_ARRAY_UNDO_SIZE;
    assert(n < MAX_ARRAY_UNDO_SIZE);
    stack->data = (array_undo_t *) safe_malloc(n * sizeof(array_undo_t));
    stack->size = n;
  } else {
    n ++;
    n += n>>1;
    if (n >= MAX_ARRAY_UNDO_SIZE) {
      out_of_memory();
    }
    stack->data = (array_undo_t *) safe_realloc(stack->data, n * sizeof(array_undo_t));
    stack->size = n;
  }
}


/*
 * Free memory
 */
static void delete_array_undo_stack(array_undo_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Reset: empty the stack
 */
static inline void reset_array_undo_stack(array_undo_stack_t *stack) {
  stack->top = 0;
}


/*
 * Push (idx, x) on top of the stack
 */
static void array_undo_stack_push_int32(array_undo_stack_t *stack, int32_t idx, int32_t x) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_array_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].index = idx;
  stack->data[i].saved.i32 = x;
  stack->top = i+1;
}


static void array_undo_stack_push_uint8(array_undo_stack_t *stack, int32_t idx, uint32_t x) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_array_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].index = idx;
  stack->data[i].saved.u8 = x;
  stack->top = i+1;
}



/*
 * TRAIL STACK
 */

/*
 * Initialize: empty stack
 */
static void init_array_trail(array_trail_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->undo_top = NULL;
}


/*
 * Increase the size:
 * - allocate the initial data array if size = 0
 * - make the stack 50% larger otherwise
 */
static void extend_array_trail(array_trail_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_ARRAY_TRAIL_SIZE;
    assert(n < MAX_ARRAY_TRAIL_SIZE);
    stack->undo_top = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
    stack->size = n;
  } else {
    n ++;
    n += (n >> 1);
    if (n >= MAX_ARRAY_TRAIL_SIZE) {
      out_of_memory();
    }
    stack->undo_top = (uint32_t *) safe_realloc(stack->undo_top, n * sizeof(uint32_t));
    stack->size = n;
  }
}


/*
 * Delete: free memory
 */
static void delete_array_trail(array_trail_t *stack) {
  safe_free(stack->undo_top);
  stack->undo_top = NULL;
}


/*
 * Reset: empty the stack
 */
static inline void reset_array_trail(array_trail_t *stack) {
  stack->top = 0;
}


/*
 * Push k on top of the trail stack
 */
static void array_trail_push(array_trail_t *stack, uint32_t k) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_array_trail(stack);
  }
  assert(i < stack->size);
  stack->undo_top[i] = k;
  stack->top = i+1;
}


/*
 * Get top element and remove it from the stack
 */
static inline uint32_t array_trail_pop(array_trail_t *stack) {
  assert(stack->top > 0);
  stack->top --;
  return stack->undo_top[stack->top];
}


/*
 * ARRAYS WITH 32bit ELEMENTS
 */

/*
 * Initialize:
 * - def = default value
 * - n = initial size. If n=0, DEF_INT32_ARRAY_SIZE is used.
 * - the initial array maps everything to def
 */
void init_int32_array(int32_array_t *a, int32_t def, uint32_t n) {
  if (n == 0) {
    n = DEF_INT32_ARRAY_SIZE;
  }

  if (n >= MAX_INT32_ARRAY_SIZE) {
    out_of_memory();
  }

  a->map = (int32_t *) safe_malloc(n * sizeof(int32_t));
  a->def = def;
  a->top = 0;
  a->size = n;
  init_array_undo_stack(&a->undo);
  init_array_trail(&a->trail);
}



/*
 * Delete: free memory
 */
void delete_int32_array(int32_array_t *a) {
  safe_free(a->map);
  a->map = NULL;
  delete_array_undo_stack(&a->undo);
  delete_array_trail(&a->trail);
}


/*
 * Reset to the initial map
 */
void reset_int32_array(int32_array_t *a) {
  a->top = 0;
  reset_array_undo_stack(&a->undo);
  reset_array_trail(&a->trail);
}


/*
 * Push: start a new level.
 */
void int32_array_push(int32_array_t *a) {
  array_trail_push(&a->trail, a->undo.top);
}


/*
 * Pop: restore the array to what it was on the matching 'push' operation.
 * - the trail stack must be non-empty.
 */
void int32_array_pop(int32_array_t *a) {
  array_undo_t *u;
  uint32_t i, n;

  n  = array_trail_pop(&a->trail);
  i = a->undo.top;
  while (i > n) {
    i --;
    u = a->undo.data + i;
    assert(u->index < a->top);
    a->map[u->index] = u->saved.i32;
  }
  a->undo.top = n;
}


/*
 * Make map large enough to write at index i
 */
static void int32_array_resize(int32_array_t *a, uint32_t i) {
  uint32_t n;

  n = a->size;
  if (n <= i) {
    n += (n >> 1);  // try 50% larger
    if (n <= i) {
      n = i+1;      // 50% is not enough
    }

    if (n >= MAX_INT32_ARRAY_SIZE) {
      out_of_memory();
    }

    a->map = (int32_t *) safe_realloc(a->map, n * sizeof(int32_t));
    a->size = n;
  }
}


/*
 * Store the default value in map[j] for j:= a->top to i
 */
static void int32_array_set_default(int32_array_t *a, uint32_t i, uint32_t def) {
  uint32_t j;
  int32_t *map;

  map = a->map;
  for (j=a->top; j<=i; j++) {
    map[j] = def;
  }
}


/*
 * Store x in a[i].
 * - save the previous value of a[i] if necessary
 */
void ai32_write(int32_array_t *a, int32_t i, int32_t x) {
  assert(0 <= i);

  if (i >= a->top) {
    int32_array_resize(a, i);
    int32_array_set_default(a, i, a->def);
    a->top = i+1;
  }

  assert(i < a->size);
  if (a->trail.top > 0) {
    array_undo_stack_push_int32(&a->undo, i, a->map[i]);
  }
  a->map[i] = x;
}




/*
 * ARRAYS WITH 8bit UNSIGNED ELEMENTS
 */

/*
 * Initialize:
 * - def = default value
 * - n = initial size. If n=0, DEF_UINT8_ARRAY_SIZE is used.
 * - the initial array maps everything to def
 */
void init_uint8_array(uint8_array_t *a, uint8_t def, uint32_t n) {
  if (n == 0) {
    n = DEF_UINT8_ARRAY_SIZE;
  }

  if (n >= MAX_UINT8_ARRAY_SIZE) {
    out_of_memory();
  }

  a->map = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  a->def = def;
  a->top = 0;
  a->size = n;
  init_array_undo_stack(&a->undo);
  init_array_trail(&a->trail);
}



/*
 * Delete: free memory
 */
void delete_uint8_array(uint8_array_t *a) {
  safe_free(a->map);
  a->map = NULL;
  delete_array_undo_stack(&a->undo);
  delete_array_trail(&a->trail);
}


/*
 * Reset to the initial map
 */
void reset_uint8_array(uint8_array_t *a) {
  a->top = 0;
  reset_array_undo_stack(&a->undo);
  reset_array_trail(&a->trail);
}


/*
 * Push: start a new level.
 */
void uint8_array_push(uint8_array_t *a) {
  array_trail_push(&a->trail, a->undo.top);
}


/*
 * Pop: restore the array to what it was on the matching 'push' operation.
 * - the trail stack must be non-empty.
 */
void uint8_array_pop(uint8_array_t *a) {
  array_undo_t *u;
  uint32_t i, n;

  n = array_trail_pop(&a->trail);
  i = a->undo.top;
  while (i > n) {
    i --;
    u = a->undo.data + i;
    assert(u->index < a->top);
    a->map[u->index] = u->saved.u8;
  }
  a->undo.top = n;
}



/*
 * Make map large enough to write at index i
 */
static void uint8_array_resize(uint8_array_t *a, uint32_t i) {
  uint32_t n;

  n = a->size;
  if (n <= i) {
    n += (n >> 1);  // try 50% larger
    if (n <= i) {
      n = i+1;      // 50% is not enough
    }

    if (n >= MAX_UINT8_ARRAY_SIZE) {
      out_of_memory();
    }

    a->map = (uint8_t *) safe_realloc(a->map, n * sizeof(uint8_t));
    a->size = n;
  }
}


/*
 * Store the default value in map[j] for j:= a->top to i
 */
static void uint8_array_set_default(uint8_array_t *a, uint32_t i, uint8_t def) {
  uint32_t j;
  uint8_t *map;

  map = a->map;
  for (j=a->top; j<=i; j++) {
    map[j] = def;
  }
}



/*
 * Store x in a[i].
 * - save the previous value of a[i] if necessary
 */
void au8_write(uint8_array_t *a, int32_t i, uint8_t x) {
  assert(0 <= i);

  if (i >= a->top) {
    uint8_array_resize(a, i);
    uint8_array_set_default(a, i, a->def);
    a->top = i+1;
  }

  assert(i < a->size);
  if (a->trail.top > 0) {
    array_undo_stack_push_uint8(&a->undo, i, a->map[i]);
  }
  a->map[i] = x;
}

