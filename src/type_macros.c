/*
 * TYPE MACROS
 */

#include "memalloc.h"
#include "refcount_strings.h"
#include "type_macros.h"


/*
 * Finalizer for names in the symbol table. This is called
 * whenever a record is removed from the symbol table.
 * All names must have a reference counter (cf. refcount_strings.h).
 */
static void macro_name_finalizer(stbl_rec_t *r) {
  string_decref(r->string);
}


/*
 * Allocate and initialize a macro descriptor:
 * - n = arity
 * - vars = array of n type variables
 * - body = type index
 */
static type_macro_t *new_descriptor(char *name, uint32_t n, type_t *vars, type_t body) {
  type_macro_t *tmp;
  uint32_t i;

  assert(n <= TYPE_MACRO_MAX_ARITY);
  tmp = (type_macro_t *) safe_malloc(sizeof(type_macro_t) + n * sizeof(type_t));
  tmp->name = name; // We don't need to increment the ref counter here.
  tmp->arity = n;
  tmp->body = body;
  for (i=0; i<n; i++) {
    tmp->vars[i] = vars[i];
  }

  return tmp;
}


/*
 * Same thing for an uninterpreted type constructor
 * - n = arity
 */
static type_macro_t *new_constructor(char *name, uint32_t n) {
  type_macro_t *tmp;

  tmp  = (type_macro_t *) safe_malloc(sizeof(type_macro_t));
  tmp->name = name; // no ref count increment required
  tmp->arity = n;
  tmp->body = NULL_TYPE;

  return tmp;
}


/*
 * Delete a descriptor
 */
static inline void delete_descriptor(type_macro_t *d) {
  safe_free(d);
}


/*
 * Initialize the macro table
 * - n = initial size
 * - ttbl = type table
 * - if n is zero, nothing is allocated yet.
 *   an array data of default size will be allocated
 *   on the first addition.
 */
void init_type_mtbl(type_mtbl_t *table, uint32_t n, type_table_t *ttbl) {
  void **tmp;

  tmp = NULL;
  if (n > 0) {
    if (n > TYPE_MACRO_MAX_SIZE) {
      out_of_memory();
    }
    tmp = (void **) safe_malloc(n * sizeof(void));
  }

  table->types = ttbl;
  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->free_idx = -1;

  init_stbl(&table->stbl, 0);
  init_tuple_hmap(&table->cache, 0);

  stbl_set_finalizer(&table->stbl, macro_name_finalizer);
}


/*
 * Delete the table and its content
 */
void delete_type_mtbl(type_mtbl_t *table) {
  void *p;
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (! has_int_tag(p)) {
      delete_descriptor(p);
    }
  }
 
  safe_free(table->data);
  table->data = NULL;

  delete_stbl(&table->stbl);
  delete_tuple_hmap(&table->cache);
}


/*
 * Empty the table: delete all macros and macro instances
 */
void reset_type_mtbl(type_mtbl_t *table) {
  void *p;
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (! has_int_tag(p)) {
      delete_descriptor(p);
    }
  }

  table->nelems = 0;
  table->free_idx = -1;

  reset_stbl(&table->stbl);
  reset_tuple_hmap(&table->cache);
}


/*
 * Make the table larger
 * - if this is the first allocation: allocate a data array of default size
 * - otherwise, make the data array 50% larger
 */
static void extend_type_mtbl(type_mtbl_t *table) {
  void **tmp;
  uint32_t n;

  n = table->size;
  if (n == 0) {
    n = TUPLE_HMAP_DEF_SIZE;
    assert(n <= TYPE_MACRO_MAX_SIZE);
    tmp = (void **) safe_malloc(n * sizeof(void*));
  } else {
    n ++;
    n += n>>1;
    if (n > TYPE_MACRO_MAX_SIZE) {
      out_of_memory();
    }
    tmp = (void **) safe_realloc(table->data, n * sizeof(void*));
  }

  table->data = tmp;
  table->size = n; 
}


/*
 * Get a macro index
 */
static int32_t allocate_macro_id(type_mtbl_t *table) {
  int32_t i;

  i = table->free_idx;
  if (i >= 0) {
    assert(i < table->nelems);
    table->free_idx = untag_i32(table->data[i]);
  } else {
    i = table->nelems;
    table->nelems ++;
    if (i >= table->size) {
      extend_type_mtbl(table);
      assert(i < table->size);
    }
  }

  return i;
}


/*
 * Delete descriptor id and add it to the free list
 * - this must be the index of a live descriptor
 */
static void free_macro_id(type_mtbl_t *table, int32_t id) {
  assert(good_type_macro(table, id));
  delete_descriptor(table->data[id]);
  table->data[id] = tag_i32(table->free_idx);
  table->free_idx = id;
}


/*
 * Add a macro descriptor:
 * - name = macro name
 * - n = arity. It must be no more than TYPE_MACRO_MAX_ARITY
 * - vars = array of n type variables (must be all distinct)
 * - body = type
 */
void add_type_macro(type_mtbl_t *table, char *name, uint32_t n, type_t *vars, type_t body) {
  type_macro_t *d;
  int32_t i;

  assert(body != NULL_TYPE);

  i = allocate_macro_id(table);
  d = new_descriptor(name, n, vars, body);
  assert(! has_int_tag(d));
  table->data[i] = d;

  stbl_add(&table->stbl, name, i);
  string_incref(name);
}


/*
 * Add an uninterpreted type constructor:
 * - name = macro name
 * - n = arity. It must be no more than TYPE_MACRO_MAX_ARITY
 */
void add_type_constructor(type_mtbl_t *table, char *name, uint32_t n) {
  type_macro_t *d;
  int32_t i;

  i = allocate_macro_id(table);
  d = new_constructor(name, n);
  assert(! has_int_tag(d));
  table->data[i] = d;
  
  stbl_add(&table->stbl, name, i);
  string_incref(name);
}


/*
 * Get a macro id of the given name
 * - return -1 if there's no macro with this name
 */
int32_t get_type_macro_by_name(type_mtbl_t *table, const char *name) {
  return stbl_find(&table->stbl, name);
}


/*
 * Remove the current mapping of 'name' to a macro id
 * - no change if 'name' does not refer to any macro
 * - otherwise, the current reference for 'name' is removed
 *   and the previous mapping is restored (if any).
 */
void remove_type_macro_name(type_mtbl_t *table, const char *name) {
  stbl_remove(&table->stbl, name);
}


/*
 * Macro instance: apply a macro to the given actual parameters
 * - id = macro id
 * - n = number of actuals
 * - actual = array of n types (actual parameters)
 * - each parameter must be a valid type 
 * - n must be equal to the macro arity.
 *
 * This first check, if this instance already exists in table->hmap.
 * If so, the instance is returned.
 *
 * Otherwise;
 * - if the macro is a type constructor (i.e., body = NULL_TYPE) 
 *   then a new uninterpreted type is returned.
 * - if the macro is a normal macro (body != NULL_TYPE), then
 *   the instance is constructed by subsituting the actuals
 *   for the macro variable.
 * In both case, the instance is stored in table->hmap
 */
type_t instantiate_type_macro(type_mtbl_t *table, int32_t id, uint32_t n, type_t *actual) {
  int32_t aux[10];
  int32_t *key;
  tuple_hmap_rec_t *r;
  type_macro_t *d;
  bool new;
  uint32_t i;
  type_t result;


  /*
   * By default, we use a buffer of 10 integers to store id + actuals 
   * If more is needed, a larger array is allocated here.
   */
  key = aux;
  if (n > 9) {
    key = (int32_t *) safe_malloc((n+1) * sizeof(int32_t));
  }

  key[0] = id;
  for (i=0; i<n; i++) {
    key[1 + i] = actual[i];
  }
  
  r = tuple_hmap_get(&table->cache, n+1, key, &new);
  result = r->value;
  if (new) {
    // new instance
    d = type_macro(table, id);
    assert(d->arity == n);
    if (d->body == NULL_TYPE) {
      result = new_uninterpreted_type(table->types);
    } else {
      result = type_substitution(table->types, d->body, n, d->vars, actual);
    }
    r->value = result;
  }

  if (n > 9) {
    safe_free(key);
  }

  return result;
}



/*
 * Keep alive function used in delete_type_macro:
 * - aux is a pointer to an integer variable and 
 *   *aux = id of the macro to delete
 * - r is a record in the tuple cache
 * - r must be deleted if its first element r->key[0] is equal to id
 */
static bool keep_cached_tuple_alive(void *aux, tuple_hmap_rec_t *r) {
  assert(r->arity > 1);
  return r->key[0] != *((int32_t *) aux);
}

/*
 * Remove macro of the given id
 * - id must be a valid macro index
 * - the macro name is deleted (from the symbol table)
 * - all instances of this macro are also deleted.
 */
void delete_type_macro(type_mtbl_t *table, int32_t id) {
  assert(good_type_macro(table, id));

  stbl_remove(&table->stbl, type_macro_name(table, id));
  tuple_hmap_gc(&table->cache, &id, keep_cached_tuple_alive);
  free_macro_id(table, id);
}
