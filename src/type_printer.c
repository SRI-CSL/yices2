/*
 * Print functions for types
 */

#include <assert.h>
#include <stdint.h>
#include <inttypes.h>

#include "type_printer.h"


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
void print_type(FILE *f, type_table_t *tbl, type_t tau) {
  char *name;
  uint32_t i, n;

  assert(good_type(tbl, tau));

  if (tau <= real_id) {
    fputs(type2string[tau], f);
  } else {
    name = type_name(tbl, tau);
    if (name != NULL) {
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
      case TUPLE_TYPE:
	fputs("(tuple", f);
	n = tuple_type_arity(tbl, tau);
	for (i=0; i<n; i++) {
	  fputc(' ', f);
	  print_type(f, tbl, tuple_type_component(tbl, tau, i));
	}
	fputc(')', f);
	break;
      case FUNCTION_TYPE:
	fputs("(-> ", f);
	n = function_type_arity(tbl, tau);
	for (i=0; i<n; i++) {
	  print_type(f, tbl, function_type_domain(tbl, tau, i));
	  fputc(' ', f);
	}
	print_type(f, tbl, function_type_range(tbl, tau));
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
 * Print type flags as a combination of 3 letters
 */
static void print_type_flags(FILE *f, uint8_t flags) {
  char c[4];

  c[0] = '-';
  c[1] = '-';
  c[2] = '-';
  c[3] = '\0';

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
      c[2] = 'L'; // large finit type
    }
  } else {
    c[2] = 'I'; // infinite type
  }

  fputs(c, f);
}


/*
 * Print the full type table
 */
void print_type_table(FILE *f, type_table_t *tbl) {
  char *name;
  uint32_t i, n, j, m;

  n = tbl->nelems;
  for (i=0; i<n; i++) {
    if (type_kind(tbl, i) != UNUSED_TYPE) {
      // flags + card
      fputc(' ', f);
      print_type_flags(f, type_flags(tbl, i));
      fprintf(f, " %10"PRIu32"   ", type_card(tbl, i));

      // name
      name = type_name(tbl, i);
      if (name != NULL) {
	fputs(name, f);
      } else {
	fprintf(f, "tau!%"PRIu32, i);
      }
      fputs(" := ", f);
      
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
	fprintf(f, "enum: card = %"PRIu32"\n", scalar_type_cardinal(tbl, i));
	break;
      case UNINTERPRETED_TYPE:
	fputs("uninterpreted\n", f);
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
      default:
	fputs("invalid type code\n", f);	
	break;
      }
    }
  }
}
