/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
 * Type id: either bool or a default id
 */
void print_type_id(FILE *f, type_t tau) {
  assert(0 <= tau);

  if (tau == bool_id) {
    fputs("bool", f);
  } else {
    fprintf(f, "tau!%"PRId32, tau);
  }
}


/*
 * Print name of type tau
 */
void print_type_name(FILE *f, type_table_t *tbl, type_t tau) {
  char *name;

  assert(good_type(tbl, tau));

  if (tau <= bool_id) {
    fputs("bool", f);
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

  assert(good_type(tbl, tau));

  switch (type_kind(tbl, tau)) {
  case BOOL_TYPE:
    fputs("bool", f);
    break;

  case BITVECTOR_TYPE:
    name = type_name(tbl, tau);
    if (name != NULL && level <= 0) {
      fputs(name, f);
    } else {
      fprintf(f, "(bitvector %"PRIu32")", bv_type_size(tbl, tau));
    }
    break;

  default:
    // DELETED TYPE
    assert(false);
    break;
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
  uint32_t i, n;
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
	fputs("bool\n", f);
        break;

      case BITVECTOR_TYPE:
        fprintf(f, "(bitvector %"PRIu32")\n", bv_type_size(tbl, i));
        break;

      default:
        fputs("invalid type code\n", f);
        break;
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

  if (tau == bool_id) {
    name = "bool";
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
  assert(good_type(tbl, tau));

  switch (type_kind(tbl, tau)) {
  case BOOL_TYPE:
    pp_string(printer, "bool");
    break;

  case BITVECTOR_TYPE:
    pp_open_block(printer, PP_OPEN_BV_TYPE);
    pp_uint32(printer, bv_type_size(tbl, tau));
    pp_close_block(printer, true);
    break;
  default:
    assert(false);
    break;
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

  init_yices_pp(&printer, f, &area, PP_VMODE, 0);

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


