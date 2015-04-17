/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MERGE TABLE: STORE EQUIVALENCE CLASSES OF VARIABLES
 */

#include "solvers/bv/merge_table.h"
#include "utils/memalloc.h"


/*
 * UNDO STACK
 */

/*
 * Initialization: nothing is allocated yet
 * - the data array is allocated on the first push
 */
static void init_mtbl_undo_stack(mtbl_undo_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}


/*
 * Make the stack larger
 * - if size = 0, allocate a data array of default size
 * - otherwise, make the array 50% larger
 */
static void extend_mtbl_undo_stack(mtbl_undo_stack_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_MTBL_UNDO_SIZE;
    assert(n < MAX_MTBL_UNDO_SIZE);
    stack->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
    stack->size = n;
  } else {
    n ++;
    n += n >> 1;
    if (n >= MAX_MTBL_UNDO_SIZE) {
      out_of_memory();
    }
    stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
    stack->size = n;
  }
}


/*
 * Delete: free memory
 */
static void delete_mtbl_undo_stack(mtbl_undo_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static inline void reset_mtbl_undo_stack(mtbl_undo_stack_t *stack) {
  stack->top = 0;
}


/*
 * Push x on top of the stack
 */
static void mtbl_undo_stack_push(mtbl_undo_stack_t *stack, int32_t x) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_mtbl_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = x;
  stack->top = i+1;
}



/*
 * TRAIL STACK
 */

/*
 * Initialize: empty stack
 */
static void init_mtbl_trail(mtbl_trail_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}

/*
 * Increase the size or allocate the initial data array
 */
static void extend_mtbl_trail(mtbl_trail_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_MTBL_TRAIL_SIZE;
    assert(n < MAX_MTBL_TRAIL_SIZE);
    stack->data = (mtbl_trail_elem_t *) safe_malloc(n * sizeof(mtbl_trail_elem_t));
    stack->size = n;
  } else {
    n ++;
    n += n >> 1;
    if (n >= MAX_MTBL_TRAIL_SIZE) {
      out_of_memory();
    }
    stack->data = (mtbl_trail_elem_t *) safe_realloc(stack->data, n * sizeof(mtbl_trail_elem_t));
    stack->size = n;
  }
}


/*
 * Free memory
 */
static void delete_mtbl_trail(mtbl_trail_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Push pair (undo_top, map_top) onto the stack
 */
static void mtbl_trail_push(mtbl_trail_t *stack, uint32_t undo_top, uint32_t map_top) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_mtbl_trail(stack);
  }
  assert(i < stack->size);
  stack->data[i].undo_top = undo_top;
  stack->data[i].map_top = map_top;
  stack->top = i+1;
}


/*
 * Remove the top element
 */
static inline void mtbl_trail_pop(mtbl_trail_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Get the top record
 */
static inline mtbl_trail_elem_t *mtbl_trail_get_top(mtbl_trail_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Check emptiness
 */
static inline bool mtbl_trail_is_empty(mtbl_trail_t *stack) {
  return stack->top == 0;
}


/*
 * Empty the stack
 */
static inline void reset_mtbl_trail(mtbl_trail_t *stack) {
  stack->top = 0;
}



/*
 * MERGE TABLE
 */

/*
 * Initialization: nothing allocated yet.
 */
void init_mtbl(mtbl_t *table) {
  table->map = NULL;
  table->top = 0;
  table->prev_top = 0;
  table->size = 0;
  init_mtbl_undo_stack(&table->undo);
  init_mtbl_trail(&table->trail);
}


/*
 * Delete the table
 */
void delete_mtbl(mtbl_t *table) {
  safe_free(table->map);
  table->map = NULL;
  delete_mtbl_undo_stack(&table->undo);
  delete_mtbl_trail(&table->trail);
}


/*
 * Reset to the empty table
 */
void reset_mtbl(mtbl_t *table) {
  table->top = 0;
  table->prev_top = 0;
  reset_mtbl_undo_stack(&table->undo);
  reset_mtbl_trail(&table->trail);
}


/*
 * Start a new level
 */
void mtbl_push(mtbl_t *table) {
  mtbl_trail_push(&table->trail, table->undo.top, table->top);
  table->prev_top = table->top;
}


/*
 * Return to the previous level
 */
void mtbl_pop(mtbl_t *table) {
  mtbl_trail_elem_t *r;
  int32_t *undo_data;
  uint32_t i, n;
  int32_t x;

  r = mtbl_trail_get_top(&table->trail);

  /*
   * Reset map[x] to -1 for all x on the undo stack for the current level
   */
  undo_data = table->undo.data;
  n = table->undo.top;
  for (i=r->undo_top; i<n; i++) {
    x = undo_data[i];
    assert(0 <= x && x < r->map_top);
    table->map[x] = -1;
  }

  table->top = r->map_top;
  table->undo.top = r->undo_top;

  mtbl_trail_pop(&table->trail);
  if (mtbl_trail_is_empty(&table->trail)) {
    table->prev_top = 0;
  } else {
    table->prev_top = mtbl_trail_get_top(&table->trail)->map_top;
  }
}


/*
 * Root of x
 */
int32_t mtbl_get_root(mtbl_t *table, int32_t x) {
  int32_t y;

  assert(x >= 0);

  while (x < table->top) {
    y = table->map[x];
    if (y < 0) break;
    x = y;
  }

  return x;
}


/*
 * Check whether x and y are in the same class
 */
bool mtbl_equiv(mtbl_t *table, int32_t x, int32_t y) {
  return mtbl_get_root(table, x) == mtbl_get_root(table, y);
}


/*
 * Make the map large enough to write map[i]
 * - do nothing if the map is large enough already
 * - if the current size is 0, try the default size first
 * - otherwise, try to double the size
 */
static void resize_mtbl(mtbl_t *table, uint32_t i) {
  uint32_t n;

  assert(i < UINT32_MAX); // so that i+1 does not overflow

  n = table->size;
  if (n <= i) {
    n <<= 1;
    if (n == 0) n = DEF_MTBL_MAP_SIZE;
    if (n <= i) n = i+1;

    if (n >= MAX_MTBL_MAP_SIZE) {
      out_of_memory();
    }

    table->map = (int32_t *) safe_realloc(table->map, n * sizeof(int32_t));
    table->size = n;
  }
}


/*
 * Increase table->top to i+1: initialize map[j] to -1 for j in top ... i
 */
static void mtbl_increase_top(mtbl_t *table, uint32_t i) {
  uint32_t j;

  assert(table->top <= i && i < table->size);

  for (j=table->top; j<=i; j++) {
    table->map[j] = -1;
  }
  table->top = j;
}




/*
 * Store y as parent of x
 * - both x and y must be non-negative
 * - x must not be mapped to anything yet (i.e., either map[x] = -1 or x >= table->top)
 * - y must be distinct from x
 */
void mtbl_map(mtbl_t *table, int32_t x, int32_t y) {
  assert(0 <= x && 0 <= y && x != y && mtbl_is_root(table, x));

  if (x < table->top) {
    assert(x < table->size && table->map[x] == -1);
    table->map[x] = y;
    if (x < table->prev_top) {
      mtbl_undo_stack_push(&table->undo, x);
    }

  } else {
    resize_mtbl(table, x);
    mtbl_increase_top(table, x);
    assert(x < table->top && x < table->size);
    table->map[x] = y;

    // no need to save x since x >= table->prev_top
    assert(x >= table->prev_top);
  }
}




