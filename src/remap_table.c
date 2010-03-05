/***************************
 *  LITERAL MAPPING TABLE  *
 **************************/

#include "remap_table.h"


/*
 * Initialization: create a table of default size
 * - create var 0 mapped to true_literal
 */
void init_remap_table(remap_table_t *table) {
  uint32_t n;

  n = DEF_REMAP_TABLE_SIZE;
  assert(0 < n && n < MAX_REMAP_TABLE_SIZE);

  table->nvars = 1;
  table->size = n;
  table->remap = (literal_t *) safe_malloc(n * sizeof(literal_t));
  table->merge_bit = allocate_bitvector(n);

  table->remap[0] = true_literal;
  clr_bit(table->merge_bit, 0);
}


/*
 * Make the table larger
 */
static void extend_remap_table(remap_table_t *table) {
  uint32_t n;

  n = table->size * 2;
  if (n >= MAX_REMAP_TABLE_SIZE) {
    out_of_memory();
  }
  table->size = n;
  table->remap = (literal_t *) safe_realloc(table->remap, n * sizeof(literal_t));
  table->merge_bit = extend_bitvector(table->merge_bit, n);
}


/*
 * Delete
 */
void delete_remap_table(remap_table_t *table) {
  safe_free(table->remap);
  delete_bitvector(table->merge_bit);
  table->remap = NULL;
  table->merge_bit = NULL;
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
  table->remap[i] = null_literal;
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
  tmp = (literal_t *) safe_malloc(n * sizeof(literal_t));
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
    // if l = pos(v), replace l by remap[v]
    // if l = neg(v), replace l by not(remap[v])
    assert(table->remap[var_of(l)] != null_literal);    
    l = table->remap[var_of(l)] ^ sign_of_lit(l);
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
    (table->remap[var_of(l1)] == null_literal || table->remap[var_of(l2)] == null_literal);
}

/*
 * Merge l1 and l2: 
 * - both must be root and l1 must be different from l2 and not(l2)
 * - if remap[l1] != null_literal, we use l2 := l1 
 * - otherwise, we map l1 to l2
 */
void remap_table_merge(remap_table_t *table, literal_t l1, literal_t l2) {
  assert(remap_table_is_root(table, l1) && remap_table_is_root(table, l2) && 
	 var_of(l1) != var_of(l2));

  if (table->remap[var_of(l1)] == null_literal) {
    // l1 := l2
    table->remap[var_of(l1)] = l2 ^ sign_of_lit(l1);
    set_bit(table->merge_bit, var_of(l1));
  } else {
    // l1 is a constant: l2 := l1
    assert(table->remap[var_of(l2)] == null_literal);
    table->remap[var_of(l2)] = l1 ^ sign_of_lit(l2);
    set_bit(table->merge_bit, var_of(l2));
  }
}


