/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>
#include <assert.h>

#include "app_reps.h"
#include "terms/types.h"
#include "utils/memalloc.h"
#include "utils/hash_functions.h"

bool app_reps_is_uf(term_table_t* terms, term_t t) {
  term_t t_kind = term_kind(terms, t);
  switch (t_kind) {
  case APP_TERM:
  case ARITH_RDIV:
  case ARITH_IDIV:
  case ARITH_MOD:
    return true;
  default:
    return false;
  }
}

type_t app_reps_get_uf_type(app_reps_t* table, term_t app_term) {
  term_table_t* terms = table->terms;
  type_table_t* types = terms->types;
  term_t app_kind = term_kind(terms, app_term);
  switch (app_kind) {
  case APP_TERM: {
    term_t f = app_reps_get_uf(terms, app_term);
    return term_type(terms, f);
  }
  case ARITH_RDIV: {
    // Div by 0 is a function from reals to reals, f(x) = x/0
    type_t reals = real_type(terms->types);
    return function_type(types, reals, 1, &reals);
  }
  case ARITH_IDIV:
  case ARITH_MOD: {
    // Div by 0 is a function from ints to ints, f(x) = x/0
    type_t ints = int_type(types);
    return function_type(types, ints, 1, &ints);
  }
  default:
    assert(false);
  }
  return NULL_TYPE;
}


composite_term_t* app_reps_get_uf_descriptor(term_table_t* terms, term_t app_term) {
  term_t app_kind = term_kind(terms, app_term);
  switch (app_kind) {
  case APP_TERM:
    return app_term_desc(terms, app_term);
  case ARITH_RDIV:
    return arith_rdiv_term_desc(terms, app_term);
  case ARITH_IDIV:
    return arith_idiv_term_desc(terms, app_term);
  case ARITH_MOD:
    return arith_mod_term_desc(terms, app_term);
    break;
  default:
    assert(false);
    return NULL;
  }
}

int32_t app_reps_get_uf(term_table_t* terms, term_t app_term) {
  term_t app_kind = term_kind(terms, app_term);
  switch (app_kind) {
  case APP_TERM:
    return app_term_desc(terms, app_term)->arg[0];
  case ARITH_RDIV:
    return APP_REP_RDIV_ID;
  case ARITH_IDIV:
    return APP_REP_IDIV_ID;
  case ARITH_MOD:
    return APP_REP_MOD_ID;
    break;
  default:
    assert(false);
    return 0;
  }
}

uint32_t app_reps_get_uf_start(term_table_t* terms, term_t app_term) {
  term_t app_kind = term_kind(terms, app_term);
  switch (app_kind) {
  case APP_TERM:
    return 1;
  default:
    return 0;
  }
}

/** Compute the has of a fully assigned function applications */
static
uint32_t compute_app_hash(app_reps_t* app_reps, variable_t f_app, bool* fully_assigned) {
  term_table_t* terms = app_reps->terms;
  variable_db_t* var_db = app_reps->var_db;
  const mcsat_trail_t* trail = app_reps->trail;

  // Get the term
  term_t f_app_term = variable_db_get_term(app_reps->var_db, f_app);

  // Get the children
  composite_term_t* desc = app_reps_get_uf_descriptor(terms, f_app_term);
  uint32_t arg_hash[desc->arity]; // Should be small
  arg_hash[0] = app_reps_get_uf(terms, f_app_term);
  uint32_t i = app_reps_get_uf_start(terms, f_app_term);
  for (; i < desc->arity; ++ i) {
    variable_t arg_i = variable_db_get_variable(var_db, desc->arg[i]);
    if (!trail_has_value(trail, arg_i)) {
      *fully_assigned = false;
      return 0;
    }
    const mcsat_value_t* arg_i_value = trail_get_value(trail, arg_i);
    arg_hash[i] = mcsat_value_hash(arg_i_value);
  }

  // Fully assigned
  *fully_assigned = true;

  // Get the hash
  return jenkins_hash_array(arg_hash, desc->arity, 0);
}

/** Compare two fully assigned function applications */
bool apps_equal(app_reps_t* app_reps, variable_t f1, variable_t f2) {
  term_table_t* terms = app_reps->terms;
  variable_db_t* var_db = app_reps->var_db;
  const mcsat_trail_t* trail = app_reps->trail;

  // Get the term
  term_t f1_term = variable_db_get_term(app_reps->var_db, f1);
  term_t f2_term = variable_db_get_term(app_reps->var_db, f2);

  // Get the children
  composite_term_t* f1_desc = app_reps_get_uf_descriptor(terms, f1_term);
  composite_term_t* f2_desc = app_reps_get_uf_descriptor(terms, f2_term);
  // Check heads
  if (app_reps_get_uf(terms, f1_term) != app_reps_get_uf(terms, f2_term)) {
    return false;
  }
  if (f1_desc->arity != f2_desc->arity) {
    return false;
  }
  uint32_t i = app_reps_get_uf_start(terms, f1_term);
  uint32_t n = f1_desc->arity;
  for (; i < n; ++ i) {
    variable_t f1_i = variable_db_get_variable(var_db, f1_desc->arg[i]);
    assert(trail_has_value(trail, f1_i));
    variable_t f2_i = variable_db_get_variable(var_db, f2_desc->arg[i]);
    assert(trail_has_value(trail, f2_i));
    // If terms equal, go next
    if (f1_i == f2_i) {
      continue;
    }
    // Compare values
    const mcsat_value_t* f1_i_value = trail_get_value(trail, f1_i);
    const mcsat_value_t* f2_i_value = trail_get_value(trail, f2_i);
    if (!mcsat_value_eq(f1_i_value, f2_i_value)) {
      return false;
    }
  }

  // All equal, we're done
  return true;
}


/*
 * Default initial size
 */
#define APP_REPS_DEFAULT_SIZE 64

/*
 * Maximal size: we want to ensure no numerical overflow when
 * computing n * sizeof(int_hrec_t)
 */
#define MAX_APP_REPS_SIZE (UINT32_MAX/sizeof(app_rep_t))


/*
 * Ratios: resize_threshold = size * RESIZE_RATIO
 *         cleanup_threshold = size * CLEANUP_RATIO
 */
#define RESIZE_RATIO 0.6
#define CLEANUP_RATIO 0.2

#define DELETED_VALUE -2
#define NULL_VALUE -1

/*
 * Initialize table: n = initial size (must be a power of 2)
 * If n = 0 set size = default value
 */
void app_reps_construct(app_reps_t *table, uint32_t n, variable_db_t* var_db, const mcsat_trail_t* trail, term_table_t* terms) {
  uint32_t i;
  app_rep_t *tmp;

  table->trail = trail;
  table->var_db = var_db;
  table->terms = terms;

  init_ivector(&table->reps, 0);
  init_ivector(&table->hashes, 0);
  scope_holder_construct(&table->scope);

  if (n == 0) {
    n = APP_REPS_DEFAULT_SIZE;
  }

  if (n >= MAX_APP_REPS_SIZE) {
    out_of_memory(); // abort
  }

  tmp = (app_rep_t *) safe_malloc(n * sizeof(app_rep_t));
  for (i=0; i<n; i++) {
    tmp[i].app_term = NULL_VALUE;
  }

  table->records = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t)(n * RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t)(n * CLEANUP_RATIO);
}

void app_reps_destruct(app_reps_t *table) {
  safe_free(table->records);
  table->records = NULL;
  delete_ivector(&table->reps);
  delete_ivector(&table->hashes);
  scope_holder_destruct(&table->scope);
}

void app_reps_clear(app_reps_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->records[i].app_term = NULL_VALUE;
  }

  table->nelems = 0;
  table->ndeleted = 0;
}

static
void app_reps_copy_record(app_rep_t *t, uint32_t hash, variable_t v, uint32_t mask) {
  uint32_t j;
  app_rep_t *r;

  j = hash & mask;
  for (;;) {
    r = t + j;
    if (r->app_term == NULL_VALUE) {
      r->app_term = v;
      r->hash = hash;
      return;
    }
    j ++;
    j &= mask;
  }
}


static
void app_reps_cleanup(app_reps_t *table) {
  app_rep_t *tmp;
  uint32_t j, n;
  uint32_t mask;
  variable_t v;

  n = table->size;
  tmp = (app_rep_t *) safe_malloc(n * sizeof(app_rep_t));
  for (j=0; j<n; j++) {
    tmp[j].app_term = NULL_VALUE;
  }

  mask = n - 1;
  for (j=0; j<n; j++) {
    v = table->records[j].app_term;
    if (v >= 0) {
      app_reps_copy_record(tmp, table->records[j].hash, v, mask);
    }
  }

  safe_free(table->records);
  table->records = tmp;
  table->ndeleted = 0;
}

static
void app_reps_extend(app_reps_t *table) {
  app_rep_t *tmp;
  uint32_t j, n, n2;
  uint32_t mask;
  variable_t v;

  n = table->size;
  n2 = n<<1;
  if (n2 == 0 || n2 >= MAX_APP_REPS_SIZE) {
    // overflow or too large
    out_of_memory();
  }

  tmp = (app_rep_t *) safe_malloc(n2 * sizeof(app_rep_t));
  for (j=0; j<n2; j++) {
    tmp[j].app_term = NULL_VALUE;
  }
  mask = n2 - 1;

  for (j=0; j<n; j++) {
    v = table->records[j].app_term;
    if (v >= 0) {
      app_reps_copy_record(tmp, table->records[j].hash, v, mask);
    }
  }

  safe_free(table->records);
  table->records = tmp;
  table->ndeleted = 0;
  table->size = n2;

  // keep same fill/cleanup ratios
  table->resize_threshold = (uint32_t) (n2 * RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n2 * CLEANUP_RATIO);
}

static
void app_reps_erase(app_reps_t *table, variable_t v, uint32_t hash) {
  uint32_t mask, j;
  app_rep_t *r;

  // table must not be full, otherwise the function loops
  assert(table->size > table->nelems + table->ndeleted);

  mask = table->size - 1;
  j = hash & mask;
  for (;;) {
    r = table->records + j;
    if (r->app_term == v) break;
    if (r->app_term == NULL_VALUE) return;
    j ++;
    j &= mask;
  }

  assert(r->hash == hash && r->app_term == v);
  table->nelems --;
  table->ndeleted ++;
  r->app_term = DELETED_VALUE;
  if (table->ndeleted > table->cleanup_threshold) {
    app_reps_cleanup(table);
  }
}

static
variable_t app_reps_store_new_app(app_reps_t *table, app_rep_t *r, uint32_t hash, variable_t v) {

  // error in build is signaled by returning v < 0
  if (v >= 0) {
    table->nelems ++;
    r->hash = hash;
    r->app_term = v;

    if (table->nelems + table->ndeleted > table->resize_threshold) {
      app_reps_extend(table);
    }
  }

  ivector_push(&table->reps, v);
  ivector_push(&table->hashes, hash);

  return v;
}

variable_t app_reps_get_rep(app_reps_t *table, variable_t v_new) {
  uint32_t mask, j, k;
  variable_t v_old;
  app_rep_t *r;
  app_rep_t *aux;
  bool fully_assigned;

  assert(table->size > table->nelems + table->ndeleted);

  mask = table->size - 1;
  k = compute_app_hash(table, v_new, &fully_assigned);
  j = k & mask;

  if (!fully_assigned) {
    return variable_null;
  }

  for (;;) {
    r = table->records + j;
    v_old = r->app_term;
    if (v_old == NULL_VALUE) return app_reps_store_new_app(table, r, k, v_new);
    if (v_old == DELETED_VALUE) break;
    if (r->hash == k && apps_equal(table, v_old, v_new)) return v_old;
    j ++;
    j &= mask;
  }

  // aux will be used to store the new index if needed
  aux = r;
  for (;;) {
    j ++;
    j &= mask;
    r = table->records + j;
    v_old = r->app_term;
    if (v_old == NULL_VALUE) {
      table->ndeleted --;
      return app_reps_store_new_app(table, aux, k, v_new);
    }
    if (v_old >= 0 && r->hash == k && apps_equal(table, v_old, v_new)) return v_old;
  }
  // To satisfy compilers
  return variable_null;
}

void app_reps_push(app_reps_t *table) {

  // Remember the size
  scope_holder_push(&table->scope,
      &table->reps.size,
      NULL
  );
}

void app_reps_pop(app_reps_t *table) {

  // Get the old size
  uint32_t old_size;
  scope_holder_pop(&table->scope,
      &old_size,
      NULL
  );

  // Remove all the added elements
  while (table->reps.size > old_size) {
    variable_t app = ivector_last(&table->reps);
    ivector_pop(&table->reps);
    uint32_t hash = ivector_last(&table->hashes);
    ivector_pop(&table->hashes);
    app_reps_erase(table, app, hash);
  }
}

void app_reps_print(const app_reps_t *table, FILE *out) {
  uint32_t i, n;
  n = table->size;
  fprintf(out, "app_reps:\n");
  for (i=0; i<n; i++) {
    variable_t x = table->records[i].app_term;
    if (x != NULL_VALUE && x != DELETED_VALUE) {
      variable_db_print_variable(table->var_db, x, out);
      fprintf(out, ", hash = %d\n", table->records[i].hash);
    }
  }
}

void app_reps_gc_sweep(app_reps_t *table, const gc_info_t* gc_vars) {
  uint32_t i, n;
  n = table->size;
  for (i=0; i<n; i++) {
    variable_t x = table->records[i].app_term;
    if (x != NULL_VALUE && x != DELETED_VALUE) {
      x = gc_info_get_reloc(gc_vars, x);
      assert(x != variable_null);
      table->records[i].app_term = x;
    }
  }
  n = table->reps.size;
  for (i=0; i<n; i++) {
    variable_t x = table->reps.data[i];
    x = gc_info_get_reloc(gc_vars, x);
    assert(x != variable_null);
    table->reps.data[i] = x;
  }

}
