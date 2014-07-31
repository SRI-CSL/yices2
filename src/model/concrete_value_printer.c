/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * OUTPUT FUNCTIONS FOR CONCRETE VALUES
 */

#include <inttypes.h>

#include "io/type_printer.h"
#include "model/concrete_value_printer.h"


/*
 * Printing for each object type
 */
static inline void vtbl_print_unknown(FILE *f) {
  fputs("???", f);
}

static inline void vtbl_print_bool(FILE *f, int32_t b) {
  if (b) {
    fputs("true", f);
  } else {
    fputs("false", f);
  }
}

static inline void vtbl_print_rational(FILE *f, rational_t *v) {
  q_print(f, v);
}

static inline void vtbl_print_bitvector(FILE *f, value_bv_t *b) {
  bvconst_print(f, b->data, b->nbits);
}


/*
 * For uninterpreted constants:
 * -
 * We print a default name if there's no name given.
 */
static void vtbl_print_unint_name(FILE *f, value_table_t *table, value_t c, value_unint_t *v) {
  const char *s;

  s = v->name;
  if (s == NULL) {
    // try to get a name from the external 'unint_namer' function
    if (table->unint_namer != NULL) {
      s = table->unint_namer(table->aux_namer, v);
    }
  }

  if (s == NULL) {
    fprintf(f, "const!%"PRId32, c);
  } else {
    fputs(s, f);
  }
}


/*
 * Function: use a default name if nothing is given
 */
static void vtbl_print_fun_name(FILE *f, value_t c, value_fun_t *fun) {
  if (fun->name == NULL) {
    fprintf(f, "fun!%"PRId32, c);
  } else {
    fputs(fun->name, f);
  }
}



/*
 * For tuples, maps, and updates: recursively print elements
 */
static void vtbl_print_tuple(FILE *f, value_table_t *table, value_tuple_t *t) {
  uint32_t i, n;

  n = t->nelems;
  fputs("(mk-tuple", f);
  for (i=0; i<n; i++) {
    fputc(' ', f);
    vtbl_print_object(f, table, t->elem[i]);
  }
  fputc(')', f);
}


static void vtbl_print_map(FILE *f, value_table_t *table, value_map_t *m) {
  uint32_t i, n;

  fputc('[', f);
  n = m->arity;
  for (i=0; i<n; i++) {
    vtbl_print_object(f, table, m->arg[i]);
    fputc(' ', f);
  }
  fputs("|-> ", f);
  vtbl_print_object(f, table, m->val);
  fputc(']', f);
}


static void vtbl_print_update(FILE *f, value_table_t *table, value_update_t *u) {
  value_map_t *m;
  uint32_t i, n;

  n = u->arity;
  assert(n > 0);

  m = vtbl_map(table, u->map);
  assert(m->arity == n);

  fputs("(update ", f);
  vtbl_print_object(f, table, u->fun);
  fputs(" (", f);
  vtbl_print_object(f, table, m->arg[0]);
  for (i=1; i<n; i++) {
    fputc(' ', f);
    vtbl_print_object(f, table, m->arg[i]);
  }
  fputs(") ", f);
  vtbl_print_object(f, table, m->val);
  fputc(')', f);
}



/*
 * Print object c on stream f
 * - if c is a function also add it to the internal queue
 */
void vtbl_print_object(FILE *f, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);
  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    vtbl_print_unknown(f);
    break;
  case BOOLEAN_VALUE:
    vtbl_print_bool(f, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    vtbl_print_rational(f, &table->desc[c].rational);
    break;
  case BITVECTOR_VALUE:
    vtbl_print_bitvector(f, table->desc[c].ptr);
    break;
  case TUPLE_VALUE:
    vtbl_print_tuple(f, table, table->desc[c].ptr);
    break;
  case UNINTERPRETED_VALUE:
    vtbl_print_unint_name(f, table, c, table->desc[c].ptr);
    break;
  case FUNCTION_VALUE:
    vtbl_print_fun_name(f, c, table->desc[c].ptr);
    vtbl_push_object(table, c);
    break;
  case MAP_VALUE:
    vtbl_print_map(f, table, table->desc[c].ptr);
    break;
  case UPDATE_VALUE:
    vtbl_print_update(f, table, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}



/*
 * Format to display a function:
 * (function <name>
 *   (type (-> tau_1 ... tau_n sigma))
 *   (= (<name> x_1 ... x_n) y_1)
 *    ...
 *   (default z))
 */
static void vtbl_print_function_header(FILE *f, value_table_t *table, value_t c, type_t tau, const char *name) {
  if (name == NULL) {
    fprintf(f, "(function fun!%"PRId32"\n", c);
  } else {
    fprintf(f, "(function %s\n", name);
  }
  fprintf(f, " (type ");
  print_type(f, table->type_table, tau);
  fprintf(f, ")");
}


/*
 * Print the function c
 * - if show_default is true, also print the default value
 */
void vtbl_print_function(FILE *f, value_table_t *table, value_t c, bool show_default) {
  value_fun_t *fun;
  value_map_t *mp;
  uint32_t i, n;
  uint32_t j, m;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;

  vtbl_print_function_header(f, table, c, fun->type, fun->name);

  m = fun->arity;
  n = fun->map_size;
  for (i=0; i<n; i++) {
    fputs("\n (= (", f);
    vtbl_print_fun_name(f, c, fun);

    mp = vtbl_map(table, fun->map[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      fputc(' ', f);
      vtbl_print_object(f, table, mp->arg[j]);
    }
    fputs(") ", f);
    vtbl_print_object(f, table, mp->val);
    fputc(')', f);
  }

  if (show_default && !is_unknown(table, fun->def)) {
    fputs("\n (default ", f);
    vtbl_print_object(f, table, fun->def);
    fputs(")", f);
  }
  fputs(")\n", f);
}


/*
 * Expand update c and print it as a function
 * - name = function name to use
 * - if show_default is true, also print the default value
 */
void vtbl_normalize_and_print_update(FILE *f, value_table_t *table, const char *name, value_t c, bool show_default) {
  char fake_name[20];
  map_hset_t *hset;
  value_map_t *mp;
  value_t def;
  type_t tau;
  uint32_t i, j, n, m;

  // build the mapping for c in hset1
  vtbl_expand_update(table, c, &def, &tau);
  hset = table->hset1;
  assert(hset != NULL);

  if (name == NULL) {
    sprintf(fake_name, "fun!%"PRId32, c);
    name = fake_name;
  }

  /*
   * hset->data contains an array of mapping objects
   * hset->nelems = number of elements in hset->data
   */
  vtbl_print_function_header(f, table, c, tau, name);

  m = vtbl_update(table, c)->arity;
  n = hset->nelems;
  for (i=0; i<n; i++) {
    fprintf(f, "\n (= (%s", name);

    mp = vtbl_map(table, hset->data[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      fputc(' ', f);
      vtbl_print_object(f, table, mp->arg[j]);
    }
    fputs(") ", f);
    vtbl_print_object(f, table, mp->val);
    fputs(")", f);
  }

  if (show_default && !is_unknown(table, def)) {
    fputs("\n (default ", f);
    vtbl_print_object(f, table, def);
    fputc(')', f);
  }
  fputs(")\n", f);
}



/*
 * Print the maps defining all the queue'd functions
 * (this may recursively queue more objects and print them too).
 * - if show_default is true, print the default value for each map
 * - once all queued functions are printed, reset the queue.
 */
void vtbl_print_queued_functions(FILE *f, value_table_t *table, bool show_default) {
  int_queue_t *q;
  value_t v;

  q = &table->queue.queue;
  while (! int_queue_is_empty(q)) {
    v = int_queue_pop(q);
    vtbl_print_function(f, table, v, show_default);
  }
  vtbl_empty_queue(table);
}


/*********************
 *  PRETTY PRINTING  *
 ********************/

/*
 * Printing for each object type
 */
static inline void vtbl_pp_bitvector(yices_pp_t *printer, value_bv_t *b) {
  pp_bv(printer, b->data, b->nbits);
}


/*
 * For uninterpreted constants:
 * -
 * We print a default name if there's no name given.
 */
static void vtbl_pp_unint_name(yices_pp_t *printer, value_table_t *table, value_t c, value_unint_t *v) {
  const char *s;

  s = v->name;
  if (s == NULL) {
    // try to get a name from the external 'unint_namer' function
    if (table->unint_namer != NULL) {
      s = table->unint_namer(table->aux_namer, v);
    }
  }

  if (s == NULL) {
    pp_id(printer, "const!", c);
  } else {
    pp_string(printer, s);
  }
}


/*
 * Function: use a default name if nothing is given
 */
static void vtbl_pp_fun_name(yices_pp_t *printer, value_t c, value_fun_t *fun) {
  if (fun->name == NULL) {
    pp_id(printer, "fun!", c);
  } else {
    pp_string(printer, fun->name);
  }
}



/*
 * For tuples, maps, and updates: recursively print elements
 */
static void vtbl_pp_tuple(yices_pp_t *printer, value_table_t *table, value_tuple_t *t) {
  uint32_t i, n;

  n = t->nelems;
  pp_open_block(printer, PP_OPEN_TUPLE);
  for (i=0; i<n; i++) {
    vtbl_pp_object(printer, table, t->elem[i]);
  }
  pp_close_block(printer, true);
}


static void vtbl_pp_map(yices_pp_t *printer, value_table_t *table, value_map_t *m) {
  uint32_t i, n;

  pp_open_block(printer, PP_OPEN_PAR);
  n = m->arity;
  pp_open_block(printer, PP_OPEN_PAR);
  for (i=0; i<n; i++) {
    vtbl_pp_object(printer, table, m->arg[i]);
  }
  pp_close_block(printer, true);
  pp_string(printer, "|->");
  vtbl_pp_object(printer, table, m->val);
  pp_close_block(printer, true);
}


static void vtbl_pp_update(yices_pp_t *printer, value_table_t *table, value_update_t *u) {
  value_map_t *m;
  uint32_t i, n;

  n = u->arity;
  assert(n > 0);

  m = vtbl_map(table, u->map);
  assert(m->arity == n);

  pp_open_block(printer, PP_OPEN_UPDATE);
  vtbl_pp_object(printer, table, u->fun);
  pp_open_block(printer, PP_OPEN_PAR);
  for (i=0; i<n; i++) {
    vtbl_pp_object(printer, table, m->arg[i]);
  }
  pp_close_block(printer, true);
  vtbl_pp_object(printer, table, m->val);
  pp_close_block(printer, true);
}



/*
 * Print object c
 * - if c is a function, add it to the internal queue
 */
void vtbl_pp_object(yices_pp_t *printer, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);

  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    pp_string(printer, "???");
    break;
  case BOOLEAN_VALUE:
    pp_bool(printer, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    pp_rational(printer, &table->desc[c].rational);
    break;
  case BITVECTOR_VALUE:
    vtbl_pp_bitvector(printer, table->desc[c].ptr);
    break;
  case TUPLE_VALUE:
    vtbl_pp_tuple(printer, table, table->desc[c].ptr);
    break;
  case UNINTERPRETED_VALUE:
    vtbl_pp_unint_name(printer, table, c, table->desc[c].ptr);
    break;
  case FUNCTION_VALUE:
    vtbl_pp_fun_name(printer, c, table->desc[c].ptr);
    vtbl_push_object(table, c);
    break;
  case MAP_VALUE:
    vtbl_pp_map(printer, table, table->desc[c].ptr);
    break;
  case UPDATE_VALUE:
    vtbl_pp_update(printer, table, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}


/*
 * Format to display a function:
 * (function <name>
 *   (type (-> tau_1 ... tau_n sigma))
 *   (= (<name> x_1 ... x_n) y_1)
 *    ...
 *   (default z))
 */
static void vtbl_pp_function_header(yices_pp_t *printer, value_table_t *table, value_t c, type_t tau, const char *name) {
  pp_open_block(printer, PP_OPEN_FUNCTION);
  if (name == NULL) {
    pp_id(printer, "fun!", c);
  } else {
    pp_string(printer, name);
  }
  pp_open_block(printer, PP_OPEN_TYPE);
  pp_type(printer, table->type_table, tau);
  pp_close_block(printer, true);
}


/*
 * Print the function c
 * - if show_default is true, also print the default falue
 */
void vtbl_pp_function(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default) {
  value_fun_t *fun;
  value_map_t *mp;
  uint32_t i, n;
  uint32_t j, m;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;

  vtbl_pp_function_header(printer, table, c, fun->type, fun->name);

  m = fun->arity;
  n = fun->map_size;
  for (i=0; i<n; i++) {
    pp_open_block(printer, PP_OPEN_EQ);  // (=
    pp_open_block(printer, PP_OPEN_PAR); // (fun
    vtbl_pp_fun_name(printer, c, fun);

    mp = vtbl_map(table, fun->map[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      vtbl_pp_object(printer, table, mp->arg[j]);
    }
    pp_close_block(printer, true); // close of (fun ...
    vtbl_pp_object(printer, table, mp->val);
    pp_close_block(printer, true); // close (= ..
  }

  if (show_default && !is_unknown(table, fun->def)) {
    pp_open_block(printer, PP_OPEN_DEFAULT); // (default
    vtbl_pp_object(printer, table, fun->def);
    pp_close_block(printer, true); // close (default ..
  }
  pp_close_block(printer, true); // close (function ...
}


/*
 * Expand update c and print it as a function
 * - name = function name to use
 * - if name is NULL, it's replaced by "fun!c"
 * - if show_default is true, also print the default value
 */
void vtbl_normalize_and_pp_update(yices_pp_t *printer, value_table_t *table, const char *name, value_t c, bool show_default) {
  char fake_name[20];
  map_hset_t *hset;
  value_map_t *mp;
  value_t def;
  type_t tau;
  uint32_t i, j, n, m;

  // build the mapping for c in hset1
  vtbl_expand_update(table, c, &def, &tau);
  hset = table->hset1;
  assert(hset != NULL);

  if (name == NULL) {
    sprintf(fake_name, "fun!%"PRId32, c);
    name = fake_name;
  }

  /*
   * hset->data contains an array of mapping objects
   * hset->nelems = number of elements in hset->data
   */
  vtbl_pp_function_header(printer, table, c, tau, name);

  m = vtbl_update(table, c)->arity;
  n = hset->nelems;
  for (i=0; i<n; i++) {
    pp_open_block(printer, PP_OPEN_EQ);
    pp_open_block(printer, PP_OPEN_PAR);
    pp_string(printer, name);

    mp = vtbl_map(table, hset->data[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      vtbl_pp_object(printer, table, mp->arg[j]);
    }
    pp_close_block(printer, true); // close (name arg[0] ... arg[m-1])
    vtbl_pp_object(printer, table, mp->val);
    pp_close_block(printer, true); // close (=
  }

  if (show_default && !is_unknown(table, def)) {
    pp_open_block(printer, PP_OPEN_DEFAULT);
    vtbl_pp_object(printer, table, def);
    pp_close_block(printer, true);
  }
  pp_close_block(printer, true);
}



/*
 * Print the maps defining all the queue'd functions
 * (this may recursively queue more objects and print them too).
 * - if show_default is true, print the default value for each map
 * - once all queued functions are printed, reset the queue.
 */
void vtbl_pp_queued_functions(yices_pp_t *printer, value_table_t *table, bool show_default) {
  int_queue_t *q;
  value_t v;

  q = &table->queue.queue;
  while (! int_queue_is_empty(q)) {
    v = int_queue_pop(q);
    vtbl_pp_function(printer, table, v, show_default);
  }
  vtbl_empty_queue(table);
}

