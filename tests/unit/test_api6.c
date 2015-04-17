/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST THE PARSER FUNCTIONS
 */

/*
 * Force assert to work even if compiled with debug disabled
 */
#ifdef NDEBUG
# undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <gmp.h>

#include "api/yices_globals.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "utils/bitvectors.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"

#include "yices.h"



/*
 * Print the type table
 */
static void show_types(void) {
  printf("\n---- Type table ----\n");
  print_type_table(stdout, __yices_globals.types);
}


/*
 * Print the term table
 */
static void show_terms(void) {
  printf("\n---- Term table -----\n");
  print_term_table(stdout, __yices_globals.terms);
}


/*
 * Print location + error message
 */
static void show_error(void) {
  error_report_t *error;

  error = yices_error_report();
  printf("parser error: line %"PRIu32", column %"PRIu32"\n", error->line, error->column);
  yices_print_error(stdout);
  fflush(stdout);
}


/*
 * Test1: create type from a string
 */
static void test_parse_type(char *s) {
  type_t tau;

  printf("\nparse_type '%s'\n", s);
  fflush(stdout);
  tau = yices_parse_type(s);
  if (tau != NULL_TYPE) {
    printf("result: ");
    print_type(stdout, __yices_globals.types, tau);
    printf("\n");
    fflush(stdout);
  } else {
    show_error();
  }
}


/*
 * Test 2: create term from a string
 */
static void test_parse_term(char *s) {
  term_t t;

  printf("\nparse_term '%s'\n", s);
  fflush(stdout);
  t = yices_parse_term(s);
  if (t != NULL_TERM) {
    printf("result: ");
    print_term(stdout, __yices_globals.terms, t);
    printf("\n");
    fflush(stdout);
  } else {
    show_error();
  }
}



/*
 * Run tests
 */
int main(void) {
  yices_init();
  show_types();
  show_terms();

  test_parse_type("int");
  test_parse_type("  bool ");
  test_parse_type("\nreal");
  test_parse_type("(bitvector 103)");
  test_parse_type("(-> int int int)");
  test_parse_type("(tuple bool bool bool bool)");
  test_parse_type("(scalar A B C D)");
  test_parse_type("(scalar X)");
  test_parse_type("not_a_type");
  test_parse_type("(bitvector -1929)");
  test_parse_type("(bitvector 0)");
  test_parse_type("(bitvector 321211213456777733887738)");
  test_parse_type("(bitvector 1073741824)");
  test_parse_type("(bitvector 178447/43)");
  test_parse_type("(bitvector 31.4e1)");
  test_parse_type("(bitvector 31.4e-3)");

  test_parse_term("true");
  test_parse_term("false");
  test_parse_term("0b30043");
  test_parse_term("0b");
  test_parse_term("0b00101");
  test_parse_term("1/0");
  test_parse_term("(/ 1 0)");
  test_parse_term("(+ 1 2 3 4 5)");
  test_parse_term("(* 1 2 3 4 5)");
  test_parse_term("(not (= 1 (- 5)))");
  test_parse_term("(let ((x A) (y B))\n   (= x y))");

  show_types();
  show_terms();

  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
