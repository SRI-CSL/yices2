/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EXPERIMENTAL: TABLE OF BOOLEAN EQUALITIES
 */

#include <assert.h>

#include "scratch/booleq_table.h"
#include "utils/memalloc.h"


/*
 * Initialize table:
 * - nothing allocated yet: dsize and esize are 0
 */
void init_booleq_table(booleq_table_t *table) {
  table->def = NULL;
  table->eq = NULL;
  table->nvars = 0;
  table->dsize = 0;
  table->neqs =0;
  table->esize = 0;
}


/*
 * Increase the size of the eq array
 */
static void booleq_table_extend_eq(booleq_table_t *table) {
  uint32_t n;

  n = table->esize;
  if (n == 0) {
    // first allocation
    n = BOOLEQ_DEFAULT_ESIZE;
    assert(n > 0 && n <= BOOLEQ_MAX_ESIZE);
    table->eq = (booleq_t *) safe_malloc(n * sizeof(booleq_t));
    table->esize = n;
  } else {
    // make the table 50% larger
    n += (n >> 1) + 1;
    if (n > BOOLEQ_MAX_ESIZE) {
      out_of_memory();
    }
    table->eq = (booleq_t *) safe_realloc(table->eq, n * sizeof(booleq_t));
    table->esize = n;
  }
}


/*
 * Allocate a new eq descriptor: return its index
 */
static int32_t booleq_table_alloc_eq(booleq_table_t *table) {
  uint32_t i;

  i = table->neqs;
  if (i == table->esize) {
    booleq_table_extend_eq(table);
  }
  assert(i < table->esize);
  table->neqs = i+1;

  return i;
}


/*
 * Make the def array large enough to store def[x]
 * - initialize all new elements to -1
 */
static void booleq_table_resize_def(booleq_table_t *table, uint32_t x) {
  uint32_t i, n;

  if (x >= table->nvars) {
    n = table->dsize;
    if (x >= n) {
      // allocate a larger array
      if (n == 0) {
	n = BOOLEQ_DEFAULT_DSIZE;
      } else {
	n += (n >> 1) + 1;
      }
      if (x >= n) {
	n = x + 1;
      }
      if (n > BOOLEQ_MAX_DSIZE) {
	out_of_memory();
      }

      table->def = (int32_t *) safe_realloc(table->def, n * sizeof(int32_t));
      table->dsize = n;
    }

    for (i=table->nvars; i<=x; i++) {
      table->def[i] = -1;
    }
    table->nvars = x + 1;
  }
}




/*
 * Empty the table
 */
void reset_booleq_table(booleq_table_t *table) {
  table->nvars = 0;
  table->neqs = 0;
}


/*
 * Free all memory used
 */
void delete_booleq_table(booleq_table_t *table) {
  safe_free(table->def);
  safe_free(table->eq);
  table->def = NULL;
  table->eq = NULL;
}


/*
 * Record the constraint l := (eq a b)
 * - there must not be any definition for var_of(l)
 */
void booleq_table_record_eq(booleq_table_t *table, literal_t l, literal_t a, literal_t b) {
  bvar_t x;
  int32_t i;

  assert(l >= 0 && a >= 0 && b >= 0);

  // normalize; force l to be positive
  a ^= sign_of_lit(l);
  l ^= sign_of_lit(l);

  assert(is_pos(l));
  x = var_of(l);
  booleq_table_resize_def(table, x);
  i = booleq_table_alloc_eq(table);

  assert(table->def[x] == -1);

  table->eq[i].lit[0] = a;
  table->eq[i].lit[1] = b;
  table->def[x] = i;
}


/*
 * Check whether x has a definition in the table
 * - x must be a valid variable index (non-negative)
 */
bool boolvar_is_eq(booleq_table_t *table, bvar_t x) {
  return x < table->nvars && table->def[x] >= 0;
}


/*
 * Get the equality equivalent to l
 * - return false if there's no such equality in table
 * - return true otherwise and set *a and *b
 * If the result is true then the equivalence l <=> (eq *a *b) holds
 */
bool get_booleq(booleq_table_t *table, literal_t l, literal_t *a, literal_t *b) {
  bvar_t x;
  int32_t i;

  assert(l >= 0);

  x = var_of(l);
  if (x < table->nvars) {
    i = table->def[x];
    if (i >= 0) {
      *a = table->eq[i].lit[0] ^ sign_of_lit(l);
      *b = table->eq[i].lit[1];
      return true;
    }
  }

  return false;
}



