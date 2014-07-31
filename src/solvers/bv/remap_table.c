/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/***************************
 *  LITERAL MAPPING TABLE  *
 **************************/

#include "solvers/bv/remap_table.h"


/*
 * UNDO STACK
 */

/*
 * Initialize the stack: initial size = 0
 * - data is allocated on the first call to push
 */
static void init_remap_undo_stack(remap_undo_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}


/*
 * Make the stack larger:
 * - if size = 0, allocate an array of default size
 * - otherwise, make the array 50% larger
 */
static void extend_remap_undo_stack(remap_undo_stack_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_REMAP_UNDO_SIZE;
    assert(n < MAX_REMAP_UNDO_SIZE);
    stack->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
    stack->size = n;
  } else {
    n ++;
    n += n >> 1;
    if (n >= MAX_REMAP_UNDO_SIZE) {
      out_of_memory();
    }
    stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
    stack->size = n;
  }
}


/*
 * Free the stack
 */
static void delete_remap_undo_stack(remap_undo_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static inline void reset_remap_undo_stack(remap_undo_stack_t *stack) {
  stack->top = 0;
}


/*
 * Push x on top of the stack
 */
static void remap_undo_stack_push(remap_undo_stack_t *stack, int32_t x) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_remap_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = x;
  stack->top = i+1;
}




/*
 * TRAIL STACK
 */

/*
 * Initialize: empty stack.
 * - data is allocated on the first push
 */
static void init_remap_trail(remap_trail_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}


/*
 * Increase the stack size.
 * - if the current size is 0, allocate an array of default size
 * - otherwise, increase the stack size by 50%
 */
static void extend_remap_trail(remap_trail_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_REMAP_TRAIL_SIZE;
    assert(n < MAX_REMAP_TRAIL_SIZE);
    stack->data = (remap_trail_elem_t *) safe_malloc(n * sizeof(remap_trail_elem_t));
    stack->size = n;
  } else {
    n ++;
    n += n>>1;
    if (n >= MAX_REMAP_TRAIL_SIZE) {
      out_of_memory();
    }
    stack->data = (remap_trail_elem_t *) safe_realloc(stack->data, n * sizeof(remap_trail_elem_t));
    stack->size = n;
  }
}



/*
 * Delete: free memory
 */
static void delete_remap_trail(remap_trail_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static inline void reset_remap_trail(remap_trail_t *stack) {
  stack->top = 0;
}


/*
 * Push pair (undo_top, map_top) on top of the stack
 */
static void remap_trail_push(remap_trail_t *stack, uint32_t undo_top, uint32_t map_top) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_remap_trail(stack);
  }
  assert(i < stack->size);
  stack->data[i].undo_top = undo_top;
  stack->data[i].map_top = map_top;
  stack->top = i+1;
}


/*
 * Remove the top element
 */
static inline void remap_trail_pop(remap_trail_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Get a pointer to the top element
 */
static inline remap_trail_elem_t *remap_trail_get_top(remap_trail_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Check whether the stack is empty
 */
static inline bool remap_trail_is_empty(remap_trail_t *stack) {
  return stack->top == 0;
}




/*
 * FULL TABLE
 */

/*
 * Initialization: create a table of default size
 * - create var 0 mapped to true_literal
 */
void init_remap_table(remap_table_t *table) {
  uint32_t n;

  n = DEF_REMAP_TABLE_SIZE;
  assert(0 < n && n < MAX_REMAP_TABLE_SIZE);

  table->map = (literal_t *) safe_malloc(n * sizeof(literal_t));
  table->merge_bit = allocate_bitvector(n);
  table->nvars = 1;
  table->prev_top = 1;
  table->size = n;

  table->map[0] = true_literal;
  clr_bit(table->merge_bit, 0);

  init_remap_undo_stack(&table->undo);
  init_remap_trail(&table->trail);
}


/*
 * Make the table larger: double its size
 */
static void extend_remap_table(remap_table_t *table) {
  uint32_t n;

  n = table->size * 2;
  if (n >= MAX_REMAP_TABLE_SIZE) {
    out_of_memory();
  }
  table->size = n;
  table->map = (literal_t *) safe_realloc(table->map, n * sizeof(literal_t));
  table->merge_bit = extend_bitvector(table->merge_bit, n);
}


/*
 * Delete
 */
void delete_remap_table(remap_table_t *table) {
  safe_free(table->map);
  delete_bitvector(table->merge_bit);
  table->map = NULL;
  table->merge_bit = NULL;

  delete_remap_undo_stack(&table->undo);
  delete_remap_trail(&table->trail);
}


/*
 * Empty the table
 */
void reset_remap_table(remap_table_t *table) {
  assert(table->size > 0 && table->map[0] == true_literal);

  table->nvars = 1;
  table->prev_top = 1;

  reset_remap_undo_stack(&table->undo);
  reset_remap_trail(&table->trail);
}


/*
 * Start a new level
 */
void remap_table_push(remap_table_t *table) {
  remap_trail_push(&table->trail, table->undo.top, table->nvars);
  table->prev_top = table->nvars;
}


/*
 * Set the level to n: call push n times
 */
void remap_table_set_level(remap_table_t *table, uint32_t n) {
  while (n > 0) {
    remap_table_push(table);
    n --;
  }
}


/*
 * Return to the previous level
 */
void remap_table_pop(remap_table_t *table) {
  remap_trail_elem_t *s;
  int32_t *undo_data;
  uint32_t i, n;
  int32_t x;

  s = remap_trail_get_top(&table->trail);


  /*
   * reset map[x] to null for all x in table->undo.data[s->undo_top to table->undo.top - 1]
   */
  n = table->undo.top;
  undo_data = table->undo.data;
  for (i=s->undo_top; i<n; i++) {
    x = undo_data[i];
    assert(0 < x && x < s->map_top);
    table->map[x] = null_literal;
    clr_bit(table->merge_bit, x);
  }

  table->nvars = s->map_top;
  table->undo.top = s->undo_top;

  remap_trail_pop(&table->trail);
  if (remap_trail_is_empty(&table->trail)) {
    table->prev_top = 1;
  } else {
    table->prev_top = remap_trail_get_top(&table->trail)->map_top;
  }
}


/*
 * Allocate a new variable v
 */
static int32_t remap_table_alloc_var(remap_table_t *table) {
  uint32_t i;

  i = table->nvars;
  if (i == table->size) {
    extend_remap_table(table);
  }
  assert(i < table->size);
  table->map[i] = null_literal;
  clr_bit(table->merge_bit, i);
  table->nvars = i + 1;

  return i;
}


/*
 * Allocate a fresh pseudo literal
 */
literal_t remap_table_fresh_lit(remap_table_t *table) {
  return pos_lit(remap_table_alloc_var(table));
}


/*
 * Construct an array of n fresh pseudo literals
 */
literal_t *remap_table_fresh_array(remap_table_t *table, uint32_t n) {
  literal_t *tmp;
  uint32_t i;

  assert(n < (UINT32_MAX/sizeof(literal_t)));
  //  tmp = (literal_t *) safe_malloc(n * sizeof(literal_t));
  tmp = alloc_int_array(n);
  for (i=0; i<n; i++) {
    tmp[i] = remap_table_fresh_lit(table);
  }
  return tmp;
}


/*
 * Substitution: replace l by its root
 */
literal_t remap_table_find_root(remap_table_t *table, literal_t l) {
  assert(0 <= var_of(l) && var_of(l) < table->nvars);

  while (tst_bit(table->merge_bit, var_of(l))) {
    // if l = pos(v), replace l by map[v]
    // if l = neg(v), replace l by not(map[v])
    assert(table->map[var_of(l)] != null_literal);
    l = table->map[var_of(l)] ^ sign_of_lit(l);
  }
  return l;
}


/*
 * Check whether l1 and l2 can be merged
 */
bool remap_table_mergeable(remap_table_t *table, literal_t l1, literal_t l2) {
  assert(0 <= var_of(l1) && var_of(l1) < table->nvars &&
         0 <= var_of(l2) && var_of(l2) < table->nvars);
  return var_of(l1) != var_of(l2) &&
    (table->map[var_of(l1)] == null_literal || table->map[var_of(l2)] == null_literal);
}




/*
 * Save v on the undo stack if necessary
 */
static inline void remap_table_save(remap_table_t *table, int32_t v) {
  assert(0 <= v && v < table->nvars);
  if (v < table->prev_top) {
    remap_undo_stack_push(&table->undo, v);
  }
}



/*
 * Merge l1 and l2:
 * - both must be root and l1 must be different from l2 and not(l2)
 * - if remap[l1] != null_literal, we use l2 := l1
 * - otherwise, we map l1 to l2
 */
void remap_table_merge(remap_table_t *table, literal_t l1, literal_t l2) {
  literal_t aux;

  assert(remap_table_is_root(table, l1) && remap_table_is_root(table, l2) &&
         var_of(l1) != var_of(l2));

  if (table->map[var_of(l1)] != null_literal) {
    // swap l1 and l2
    aux = l1; l1 = l2; l2 = aux;
  }

  /*
   * If l1 is positive: store l2 as map[var_of(l1)]
   * If l1 is negative: store not(l2) in map[var_of(l1)]
   */
  assert(table->map[var_of(l1)] == null_literal);
  table->map[var_of(l1)] = l2 ^ sign_of_lit(l1);
  set_bit(table->merge_bit, var_of(l1));
  remap_table_save(table, var_of(l1));
}




/*
 * Assign real literal l to the class of l
 */
void remap_table_assign(remap_table_t *table, literal_t l, literal_t l1) {
  l = remap_table_find_root(table, l);
  assert(table->map[var_of(l)] == null_literal);

  assert(l1 != null_literal);
  table->map[var_of(l)] = l1 ^ sign_of_lit(l);
  remap_table_save(table, var_of(l));
}
