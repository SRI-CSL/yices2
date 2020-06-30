/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Print functions for types
 */

#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>

#include "io/type_printer.h"


/*
 * Ids for bool, int, and real types
 * (bool = 0, int = 1, real = 2).
 */
static const char * const type2string[] = {
  "bool", "int", "real"
};

/*
 * Type id: either bool, int, real or a default id
 */
void print_type_id(FILE *f, type_t tau) {
  assert(0 <= tau);

  if (tau <= real_id) {
    fputs(type2string[tau], f);
  } else {
    fprintf(f, "tau!%"PRId32, tau);
  }
}


/*
 * Name of macro id
 */
void print_macro_name(FILE *f, type_table_t *tbl, int32_t id) {
  type_mtbl_t *mtbl;

  mtbl = tbl->macro_tbl;
  assert(mtbl != NULL);
  fputs(type_macro_name(mtbl, id), f);
}


/*
 * Print name of type tau
 */
void print_type_name(FILE *f, type_table_t *tbl, type_t tau) {
  char *name;

  assert(good_type(tbl, tau));

  if (tau <= real_id) {
    fputs(type2string[tau], f);
  } else {
    name = type_name(tbl, tau);
    if (name != NULL) {
      fputs(name, f);
    } else {
      fprintf(f, "tau!%"PRId32, tau);
    }
  }
}


/*
 * Print type tau
 */
static void print_type_recur(FILE *f, type_table_t *tbl, type_t tau, int32_t level) {
  char *name;
  uint32_t i, n;

  assert(good_type(tbl, tau));

  if (tau <= real_id) {
    fputs(type2string[tau], f);
  } else {
    name = type_name(tbl, tau);
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      switch (type_kind(tbl, tau)) {
      case BITVECTOR_TYPE:
        fprintf(f, "(bitvector %"PRIu32")", bv_type_size(tbl, tau));
        break;
      case SCALAR_TYPE:
        fprintf(f, "(enum!%"PRId32" %"PRIu32")", tau, scalar_type_cardinal(tbl, tau));
        break;
      case UNINTERPRETED_TYPE:
        fprintf(f, "unint!%"PRId32, tau);
        break;
      case VARIABLE_TYPE:
        fprintf(f, "var!%"PRIu32, type_variable_id(tbl, tau));
        break;
      case TUPLE_TYPE:
        fputs("(tuple", f);
        n = tuple_type_arity(tbl, tau);
        for (i=0; i<n; i++) {
          fputc(' ', f);
          print_type_recur(f, tbl, tuple_type_component(tbl, tau, i), level - 1);
        }
        fputc(')', f);
        break;
      case FUNCTION_TYPE:
        fputs("(-> ", f);
        n = function_type_arity(tbl, tau);
        for (i=0; i<n; i++) {
          print_type_recur(f, tbl, function_type_domain(tbl, tau, i), level - 1);
          fputc(' ', f);
        }
        print_type_recur(f, tbl, function_type_range(tbl, tau), level - 1);
        fputc(')', f);
        break;
      case INSTANCE_TYPE:
        fputc('(', f);
        print_macro_name(f, tbl, instance_type_cid(tbl, tau));
        n = instance_type_arity(tbl, tau);
        for (i=0; i<n; i++) {
          fputc(' ', f);
          print_type_recur(f, tbl, instance_type_param(tbl, tau, i), level - 1);
        }
        fputc(')', f);
        break;
      default:
        assert(false);
        break;
      }
    }
  }
}


/*
 * Expand names only at the outer level
 */
void print_type_exp(FILE *f, type_table_t *tbl, type_t tau) {
  print_type_recur(f, tbl, tau, 1);
}


/*
 * Don't expand names
 */
void print_type(FILE *f, type_table_t *tbl, type_t tau) {
  print_type_recur(f, tbl, tau, 0);
}

/*
 * Definition: name := type
 */
void print_type_def(FILE *f, type_table_t *tbl, type_t tau) {
  print_type_name(f, tbl, tau);
  fputs(" := ", f);
  print_type_recur(f, tbl, tau, 1);
}


/*
 * Macro definition
 */
void print_macro_def(FILE *f, type_table_t *tbl, int32_t id) {
  type_macro_t *d;
  uint32_t i, n;

  d = type_macro(tbl, id);
  if (d->body == NULL_TYPE) {
    fprintf(f, "(declare-sort %s %"PRIu32")\n", d->name, d->arity);
  } else {
    fprintf(f, "(define-sort %s (", d->name);
    n = d->arity;
    assert(n >= 1);
    print_type_name(f, tbl, d->vars[0]);
    for (i=1; i<n; i++) {
      fputc(' ', f);
      print_type_name(f, tbl, d->vars[i]);
    }
    fputs(") ", f);
    print_type(f, tbl, d->body);
    fputs(")\n", f);
  }
}



/*
 * Print type flags as a combination of 34letters
 */
static void print_type_flags(FILE *f, uint8_t flags) {
  char c[5];

  c[0] = '-';
  c[1] = '-';
  c[2] = '-';
  c[3] = '-';
  c[4] = '\0';

  if (flags & TYPE_IS_MAXIMAL_MASK) {
    c[0] = 'M';
  }
  if (flags & TYPE_IS_MINIMAL_MASK) {
    c[1] = 'm';
  }
  if (flags & TYPE_IS_UNIT_MASK) {
    c[2] = 'U'; // unit type
  } else if (flags & TYPE_IS_FINITE_MASK) {
    if (flags & CARD_IS_EXACT_MASK) {
      c[2] = 'S'; // small finite type
    } else {
      c[2] = 'L'; // large finite type
    }
  } else {
    c[2] = 'I'; // infinite type
  }

  if (flags & TYPE_IS_GROUND_MASK) {
    c[3] = 'G';  // ground type
  }

  fputs(c, f);
}



/*
 * Maximal length of all names in tbl
 * - return 0 if no type has a name
 */
static uint32_t max_name_length(type_table_t *tbl) {
  char *name;
  uint32_t max, l, n, i;

  max = 0;
  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (type_kind(tbl, i) != UNUSED_TYPE) {
      name = tbl->name[i];
      if (name != NULL) {
        l = strlen(name);
        if (l > max) {
          max = l;
        }
      }
    }
  }

  return max;
}

/*
 * Print n blanks
 */
static void print_spaces(FILE *f, uint32_t n) {
  while (n > 0) {
    fputc(' ', f);
    n --;
  }
}


/*
 * Print string s, and add enough spaces to get to length l.
 * - if s is too long, print s and add one space
 */
static void print_padded_string(FILE *f, char *s, uint32_t l) {
  if (s == NULL) {
    print_spaces(f, l);
  } else if (l >= strlen(s)) {
    while (*s != '\0') {
      fputc(*s, f);
      s ++;
      l --;
    }
    print_spaces(f, l);
  } else {
    fprintf(f, "%s ", s);
  }
}


/*
 * Print the full type table
 */
void print_type_table(FILE *f, type_table_t *tbl) {
  uint32_t i, n, j, m;
  uint32_t name_size;

  name_size = max_name_length(tbl) + 2;
  if (name_size < 4) {
    name_size = 4;
  } else if (name_size > 20) {
    name_size = 20;
  }

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (type_kind(tbl, i) != UNUSED_TYPE) {
      // id, flags, card
      fprintf(f, "%4"PRIu32" ", i);
      print_type_flags(f, type_flags(tbl, i));
      fprintf(f, " %10"PRIu32"   ", type_card(tbl, i));

      // name + one space
      print_padded_string(f, type_name(tbl, i), name_size);

      // definition
      switch (type_kind(tbl, i)) {
      case BOOL_TYPE:
      case INT_TYPE:
      case REAL_TYPE:
        fputs(type2string[i], f);
        fputc('\n', f);
        break;
      case BITVECTOR_TYPE:
        fprintf(f, "(bitvector %"PRIu32")\n", bv_type_size(tbl, i));
        break;
      case SCALAR_TYPE:
        fprintf(f, "(enum, card = %"PRIu32")\n", scalar_type_cardinal(tbl, i));
        break;
      case UNINTERPRETED_TYPE:
        fputs("(uninterpreted)\n", f);
        break;
      case VARIABLE_TYPE:
        fprintf(f, "(variable, id = %"PRIu32")\n", type_variable_id(tbl, i));
        break;
      case TUPLE_TYPE:
        fputs("(tuple", f);
        m = tuple_type_arity(tbl, i);
        for (j=0; j<m; j++) {
          fputc(' ', f);
          print_type_name(f, tbl, tuple_type_component(tbl, i, j));
        }
        fputs(")\n", f);
        break;
      case FUNCTION_TYPE:
        fputs("(-> ", f);
        m = function_type_arity(tbl, i);
        for (j=0; j<m; j++) {
          print_type_name(f, tbl, function_type_domain(tbl, i, j));
          fputc(' ', f);
        }
        print_type_name(f, tbl, function_type_range(tbl, i));
        fputs(")\n", f);
        break;
      case INSTANCE_TYPE:
        fputc('(', f);
        print_macro_name(f, tbl, instance_type_cid(tbl, i));
        m = instance_type_arity(tbl, i);
        for (j=0; j<m; j++) {
          fputc(' ', f);
          print_type_name(f, tbl, instance_type_param(tbl, i, j));
        }
        fputs(")\n", f);
        break;
      default:
        fputs("invalid type code\n", f);
        break;
      }
    }
  }
}


/*
 * All macros
 */
void print_type_macros(FILE *f, type_table_t *tbl) {
  type_mtbl_t *mtbl;
  uint32_t i, n;

  mtbl = tbl->macro_tbl;
  if (mtbl != NULL) {
    n = mtbl->nelems;
    for (i=0; i<n; i++) {
      if (good_type_macro(mtbl, i)) {
        print_macro_def(f, tbl, i);
      }
    }
  }
}


/*
 * PRETTY PRINTING
 */

/*
 * Print type name
 */
void pp_type_name(yices_pp_t *printer, type_table_t *tbl, type_t tau) {
  char *name;

  assert(good_type(tbl, tau));

  if (tau <= real_id) {
    name = (char*) type2string[tau];
  } else {
    name = type_name(tbl, tau);
  }
  if (name != NULL) {
    pp_string(printer, name);
  } else {
    pp_id(printer, "tau!", tau);
  }
}


/*
 * Print type expression for tau: expand the type names if level > 0
 */
static void pp_type_recur(yices_pp_t *printer, type_table_t *tbl, type_t tau, int32_t level) {
  char *name;
  uint32_t i, n;

  assert(good_type(tbl, tau));

  if (tau <= real_id) {
    pp_string(printer, (char *) type2string[tau]);
  } else {
    name = type_name(tbl, tau);
    if (name != NULL && level <= 0) {
      pp_string(printer, name);
    } else {
      switch (type_kind(tbl, tau)) {
      case BITVECTOR_TYPE:
        pp_open_block(printer, PP_OPEN_BV_TYPE);
        pp_uint32(printer, bv_type_size(tbl, tau));
        pp_close_block(printer, true);
        break;

      case SCALAR_TYPE:
      case UNINTERPRETED_TYPE:
        if (name != NULL) {
          pp_string(printer, name);
        } else {
          pp_id(printer, "tau!", tau);
        }
        break;

      case VARIABLE_TYPE:
        if (name != NULL) {
          pp_string(printer, name);
        } else {
          pp_id(printer, "var!", type_variable_id(tbl, tau));
        }
        break;

      case TUPLE_TYPE:
        pp_open_block(printer, PP_OPEN_TUPLE_TYPE);
        n = tuple_type_arity(tbl, tau);
        for (i=0; i<n; i++) {
          pp_type_recur(printer, tbl, tuple_type_component(tbl, tau, i), level - 1);
        }
        pp_close_block(printer, true);
        break;

      case FUNCTION_TYPE:
        pp_open_block(printer, PP_OPEN_FUN_TYPE);
        n = function_type_arity(tbl, tau);
        for (i=0; i<n; i++) {
          pp_type_recur(printer, tbl, function_type_domain(tbl, tau, i), level - 1);
        }
        pp_type_recur(printer, tbl, function_type_range(tbl, tau), level - 1);
        pp_close_block(printer, true);
        break;

      case INSTANCE_TYPE:
        pp_open_block(printer, PP_OPEN_PAR);
        assert(tbl->macro_tbl != NULL);
        pp_string(printer, type_macro_name(tbl->macro_tbl, instance_type_cid(tbl, tau)));
        n = instance_type_arity(tbl, tau);
        for (i=0; i<n; i++) {
          pp_type_recur(printer, tbl, instance_type_param(tbl, tau, i), level - 1);
        }
        pp_close_block(printer, true);
        break;

      default:
        assert(false);
        break;
      }
    }
  }
}


/*
 * Expand top-level names
 */
void pp_type_exp(yices_pp_t *printer, type_table_t *tbl, type_t tau) {
  pp_type_recur(printer, tbl, tau, 1);
}


/*
 * Don't expand top-level names
 */
void pp_type(yices_pp_t *printer, type_table_t *tbl, type_t tau) {
  pp_type_recur(printer, tbl, tau, 0);
}


/*
 * Pretty printing of the full table
 */
void pp_type_table(FILE *f, type_table_t *tbl) {
  yices_pp_t printer;
  pp_area_t area;
  uint32_t i, n;

  area.width = 60;
  area.height = 2;
  area.offset = 11;
  area.truncate = true;
  area.stretch = false;

  init_yices_pp(&printer, PP_LANG_YICES, f, &area, PP_VMODE, 0);

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (type_kind(tbl, i) != UNUSED_TYPE) {
      fprintf(f, "type[%"PRIu32"]: ", i);
      if (i < 10) fputc(' ', f);
      if (i < 100) fputc(' ', f);
      pp_type(&printer, tbl, i);
      flush_yices_pp(&printer);
    }
  }

  delete_yices_pp(&printer, false);
}


