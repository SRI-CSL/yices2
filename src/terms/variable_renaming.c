/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Data structure to rename bound variables
 *
 * For a variable x, we store an array of variables x_1,...,x_n.
 * These variables are used in tun to rename x in different scopes.
 * Example: in (forall x: (and p(x) (forall x, y: q(x, y))))
 * then the first x is renamed to x_1, and the second to x_2
 * to give: (forall x_1: (and p(x_1) (forall x_2, y_1: q(x_2, y_1)))).
 *
 * We store the renaming for x in an array a of 32bit integers:
 *    a[0] = x
 *    a[1] = index k between 1 and n+1
 *    a[2] = x_1
 *    ...
 *    a[n+1] = x_n
 * This is interpreted as follows:
 * - if k=1, then x is not renamed in the current scope
 * - otherwise, x is renamed to a[k] = x_{k-1}
 */

#include <assert.h>

#include "terms/term_utils.h"
#include "terms/variable_renaming.h"
#include "utils/index_vectors.h"
#include "utils/memalloc.h"


/*
 * Initialize the renaming structure
 * - ttbl = attached term table
 * - initial size = 0
 */
void init_renaming(renaming_t *s, term_table_t *ttbl) {
  s->data = NULL;
  s->terms = ttbl;
  s->size = 0;
}


/*
 * Delete all memory used
 */
void delete_renaming(renaming_t *s) {
  int32_t **tmp;
  uint32_t i, n;

  tmp = s->data;
  n = s->size;
  for (i=0; i<n; i++) {
    if (tmp[i] == NULL) break;
    delete_index_vector(tmp[i]);
  }

  safe_free(tmp);
  s->data = NULL;
}


/*
 * Empty the array
 */
void reset_renaming(renaming_t *s) {
  int32_t **tmp;
  uint32_t i, n;

  tmp = s->data;
  n = s->size;
  for (i=0; i<n; i++) {
    if (tmp[i] == NULL) break;
    delete_index_vector(tmp[i]);
    tmp[i] = NULL;
  }
}


/*
 * Make the renaming array larger.
 * - if current size is 0, this allocates an array of default size
 * - otherwise, the size if increased by 50%
 */
static void extend_renaming(renaming_t *s) {
  int32_t **tmp;
  uint32_t i, n;

  n = s->size;
  if (n == 0) {
    n = DEF_RENAMING_SIZE;
    assert(n <= MAX_RENAMING_SIZE && s->data == NULL);
    tmp = (int32_t **) safe_malloc(n * sizeof(int32_t*));
  } else {
    n++;
    n += n>>1;
    if (n > MAX_RENAMING_SIZE) {
      out_of_memory();
    }
    tmp = (int32_t **) safe_realloc(s->data, n * sizeof(int32_t *));
  }

  for (i=s->size; i<n; i++) {
    tmp[i] = NULL;
  }

  s->data = tmp;
  s->size = n;
}


/*
 * Search for an array a in renaming for variable x:
 * - i.e. a[0] = x
 * - return NULL if there's no such array
 */
static int32_t *find_renaming_array(renaming_t *s, term_t x) {
  uint32_t i, n;
  int32_t *a;

  n = s->size;
  for (i=0; i<n; i++) {
    a = s->data[i];
    if (a == NULL || a[0] == x) return a;
  }

  return NULL;
}


/*
 * Search for an array a for variable x
 * - if there's no such array, then create a new one and add it to s
 * - return the index i such that s->data[i] = array for x
 */
static uint32_t get_renaming_array(renaming_t *s, term_t x) {
  uint32_t i, n;
  int32_t *a;

  n = s->size;
  for (i=0; i<n; i++) {
    a = s->data[i];
    if (a == NULL) goto add;
    if (a[0] == x) return i;
  }
  extend_renaming(s);

 add:
  // add new array for x in s->data[i]
  // the initial content of this array is [x, 1]
  assert(i< s->size && s->data[i] == NULL);
  add_index_to_vector(s->data + i, x);
  add_index_to_vector(s->data + i, 1);

  return i;
}


/*
 * Get the renaming of x in a new scope
 * - x must be a variable in s->terms
 * - if x is attached to x_1, ..., x_n and the current scope is i
 *   (i.e., x is currently renamed to x_i) then the scope is incremented
 *   and x_{i+1} is returned.
 * - if i=n, then a fresh variable x_{n+1} is created and returned
 * - if x is not attached to anything yet, then a fresh array a is
 *   created and x is renamed to a fresh variable x_1 that gets
 *   stored in a.
 */
term_t get_var_renaming(renaming_t *s, term_t x) {
  int32_t *a;
  term_t y;
  uint32_t i;
  int32_t k;

  assert(term_kind(s->terms, x) == VARIABLE);

  i = get_renaming_array(s, x);
  a = s->data[i];
  assert(a != NULL && iv_size(a) >= 2 && a[0] == x);

  k = a[1]; // current index for x
  k ++;
  a[1] = k;
  if (k < iv_size(a)) {
    y = a[k];
  } else {
    y = clone_variable(s->terms, x);
    add_index_to_vector(s->data + i, y);
  }

  assert(a[1] == k && 2 <= k && k < iv_size(a) && a[k] == y);

  return y;
}


/*
 * Clear the current renaming of x
 * - no change if x has not been renamed
 */
void clear_var_renaming(renaming_t *s, term_t x) {
  int32_t *a;

  assert(term_kind(s->terms, x) == VARIABLE);

  a = find_renaming_array(s, x);
  assert(a == NULL || (iv_size(a) >= 2 && a[0] == x));

  if (a != NULL && a[1] > 1) {
    a[1] --;
  }
}
