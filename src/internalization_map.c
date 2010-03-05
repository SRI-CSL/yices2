/*
 * Internalization tables
 */

#include <stdint.h>
#include <assert.h>

#include "memalloc.h"
#include "internalization_map.h"



/*****************
 *  TRAIL STACK  *
 ****************/

/*
 * Allocate and initialize a new trail stack
 * - n = its size. 
 * - if n = 0, the default size is used.
 */
static itrail_t *new_itrail(uint32_t n) {
  itrail_t *trail;

  if (n == 0) {
    n = DEFAULT_ITRAIL_SIZE;
  }

  if (n >= MAX_ITRAIL_SIZE) { 
    out_of_memory();
  }

  trail = (itrail_t *) safe_malloc(sizeof(itrail_t));
  trail->size = n;
  trail->top = 0;
  trail->top_frame = -1;
  trail->data = (int32_t *) safe_malloc(n * sizeof(int32_t));

  return trail;
}


/*
 * Delete trail stack
 */
static void delete_itrail(itrail_t *stack) {
  safe_free(stack->data);
  safe_free(stack);
}


/*
 * Reset trail stack
 */
static void reset_itrail(itrail_t *stack) {
  stack->top = 0;
  stack->top_frame = -1;
}


/*
 * Increase the size by 50%
 */
static void extend_itrail(itrail_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;

  if (n >= MAX_ITRAIL_SIZE) {
    out_of_memory();
  }

  stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
  stack->size = n;
}


/*
 * Push integer x on top of the stack
 */
static void itrail_push(itrail_t *stack, int32_t x) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_itrail(stack);
  }
  assert(i < stack->size);
  stack->data[i] = x;
  stack->top = i+1;
}


/*
 * Start a new frame
 */
static void itrail_new_frame(itrail_t *stack) {
  int32_t k;

  k = stack->top;
  itrail_push(stack, stack->top_frame);
  stack->top_frame = k;
}


/*
 * Remove the top frame:
 * stack->top_frame must be non-negative
 */
static void itrail_pop_frame(itrail_t *stack) {
  int32_t k;

  assert(stack->top_frame >= 0);

  k = stack->top_frame;
  stack->top_frame = stack->data[k];
  stack->top = k;
}




/***************************
 *  INTERNALIZATION TABLE  *
 **************************/

/*
 * Initialize table of size n
 * - if n == 0, the default size is used
 */
void init_itable(itable_t *table, uint32_t n) {
  uint32_t i;
  int32_t *tmp;

  if (n == 0) {
    n = DEFAULT_ITABLE_SIZE;
  }
  if (n >= MAX_ITABLE_SIZE) {
    out_of_memory();
  }

  tmp = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    tmp[i] = nil;
  }

  table->size = n;
  table->level = 0;
  table->data = tmp;
  table->trail = NULL;
  table->saved = NULL;
}


/*
 * Delete the table
 */
void delete_itable(itable_t *table) {
  safe_free(table->data);
  if (table->trail != NULL) {
    delete_itrail(table->trail);
    delete_bitvector(table->saved);
  }
  table->data = NULL;
  table->trail = NULL;
  table->saved = NULL;
}



/*
 * Reset the table
 */
void reset_itable(itable_t *table) {
  uint32_t i, n;

  table->level = 0;

  n = table->size;  
  for (i=0; i<n; i++) {
    table->data[i] = nil;
  }

  if (table->trail != NULL) {
    assert(table->saved != NULL);
    reset_itrail(table->trail);
    clear_bitvector(table->saved, n);
  }
}


/*
 * Allocate the trail stack and saved vector
 * - the saved vector has the same size as the table
 */
static void alloc_trail(itable_t *table) {
  uint32_t n;

  assert(table->trail == NULL && table->saved == NULL);

  n = table->size;
  table->trail = new_itrail(0);
  table->saved = allocate_bitvector0(n);
}



/*
 * Increase the table size (and the saved bit vector if it's not NULL)
 * - the new size is at least n
 * - requires n > current size
 */
static void resize_itable(itable_t *table, uint32_t n) {
  uint32_t i, new_size, old_size;
  int32_t *tmp;

  assert(table->size < n);

  // try to make the table 50% larger
  old_size = table->size;
  new_size = old_size + 1;
  new_size += new_size >> 1;
  if (new_size < n) {
    new_size = n;
  }

  if (new_size >= MAX_ITABLE_SIZE) { // could do better than this
    out_of_memory();
  }

  if (table->saved != NULL) {
    table->saved = extend_bitvector0(table->saved, new_size, old_size);
  }

  tmp = (int32_t *) safe_realloc(table->data, new_size * sizeof(int32_t));
  for (i=old_size; i<new_size; i++) {
    tmp[i] = nil;
  }
  table->data = tmp;
  table->size = new_size;
}



/*
 * Start a new frame:
 * - increase level and clear all the marks
 */
void itable_push(itable_t *table) {
  if (table->trail == NULL) {
    alloc_trail(table);
  }
  itrail_new_frame(table->trail);
  clear_bitvector(table->saved, table->size);
  table->level ++;
}


/*
 * Get what's mapped to x (nil if nothing mapped)
 */
int32_t itable_get(itable_t *table, int32_t x) {
  assert(x >= 0);
  return (x < table->size) ? table->data[x] : nil;
}



/*
 * Set a negative mark to x
 * - x must be non negative
 * - k must be negative and different from nil
 */
void itable_set_mark(itable_t *table, int32_t x, int32_t k) {
  assert(x >= 0 && k < nil && itable_get(table, x) < 0);
  
  if (x >= table->size) {
    resize_itable(table, x+1);
  }
  table->data[x] = k;
}



/*
 * Add mapping [x --> k] to the table
 * - x and k must be non-negative
 * - x must not be mapped to anything
 */
void itable_map(itable_t *table, int32_t x, int32_t k) {
  assert(x >= 0 && k >= 0 && itable_get(table, x) < 0);

  if (x >= table->size) {
    resize_itable(table, x+1);
  }
  table->data[x] = k;

  if (table->level > 0) {
    assert(! tst_bit(table->saved, x));
    itrail_push(table->trail, x);
    set_bit(table->saved, x);
  }
}


/*
 * Overwrite the current mapping for x
 * - new value is k
 * - old value is saved onto the trail stack
 */
void itable_remap(itable_t *table, int32_t x, int32_t k) {
  assert(x >= 0 && k >= 0 && x < table->size && table->data[x] >= 0);

  if (table->level > 0 && ! tst_bit(table->saved, x)) {
    /*
     * to save the old mapping [x --> old_k]:
     * we push -(x + 1) followed by old_k onto the trail stack
     */
    itrail_push(table->trail, -(x+1));
    itrail_push(table->trail, table->data[x]);
    set_bit(table->saved, x);
  }

  table->data[x] = k;
}


/*
 * Pop: restore the mapping to what it was on the previous push
 */
void itable_pop(itable_t *table) {
  itrail_t *trail;
  int32_t *aux;  
  uint32_t i, n;
  int32_t x, k;

  assert(table->level > 0 && table->trail != NULL && table->saved != NULL);

  trail = table->trail;
  aux = trail->data;

  n = trail->top;
  i = trail->top_frame + 1;
  while (i<n) {
    x = aux[i];
    if (x < 0) {
      // old mapping x --> k  saved via remap
      assert(i < n);
      i ++;
      k = aux[i];
      x = - (x + 1);
      // restore old mapping
      table->data[x] = k;
    } else {
      // mapping x --> k added via map: clear it
      table->data[x] = nil;
    }
    assert(tst_bit(table->saved, x));
    clr_bit(table->saved, x);
    i ++;
  }

  itrail_pop_frame(table->trail);
  table->level --;

  if (table->level > 0) {
    // recover the bit marks based on the frame just restored
    n = trail->top;
    i = trail->top_frame + 1;
    while (i<n) {
      x = aux[i];
      if (x < 0) {
	x = - (x + 1);
	i ++;
      }
      assert(! tst_bit(table->saved, x));
      set_bit(table->saved, x);
      i ++;
    }
  }
}



/*
 * Number of elements = x+1 where x = last index mapped to a non-nil value
 */
uint32_t itable_num_elements(itable_t *table) {
  uint32_t n;
  int32_t *map;

  map = table->data;
  n = table->size;
  while (n > 0) {
    n --;
    if (map[n] != nil) {
      return n+1;
    }
  }

  return 0;
}
