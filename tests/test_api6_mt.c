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

#include "memalloc.h"
#include "bitvectors.h"
#include "int_vectors.h"

#include "type_printer.h"
#include "term_printer.h"
#include "yices.h"
#include "yices_globals.h"

#include "threads.h"
#include "threadsafe.h"
#include "stores.h"




/*
 * Test1: create type from a string
 */
static void test_parse_type(FILE* output, char *s) {
  type_t tau;

  fprintf(output, "\nparse_type '%s'\n", s);
  fflush(output);
  tau = yices_parse_type(s);
  if (tau != NULL_TYPE) {
    fprintf(output, "result: ");
    print_type_mt(output, tau);
    fprintf(output, "\n");
    fflush(output);
  } else {
    show_error(output);
  }
}


/*
 * Test 2: create term from a string
 */
static void test_parse_term(FILE* output, char *s) {
  term_t t;

  fprintf(output, "\nparse_term '%s'\n", s);
  fflush(output);
  t = yices_parse_term(s);
  if (t != NULL_TERM) {
    fprintf(output, "result: ");
    print_term_mt(output, t);
    fprintf(output, "\n");
    fflush(output);
  } else {
    show_error(output);
  }
}



yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  FILE* output = (FILE *)arg;

  fprintf(stderr, "Starting: %s\n", "show_types");
  show_types(output);
  fprintf(stderr, "Starting: %s\n", "show_terms");
  show_terms(output);

  fprintf(stderr, "Starting: %s\n", "int");
  test_parse_type(output, "int");
  fprintf(stderr, "Starting: %s\n", "  bool ");
  test_parse_type(output, "  bool ");
  fprintf(stderr, "Starting: %s\n", "real");
  test_parse_type(output, "\nreal");
  fprintf(stderr, "Starting: %s\n", "(bitvector 103)");
  test_parse_type(output, "(bitvector 103)");
  fprintf(stderr, "Starting: %s\n", "(-> int int int)");
  test_parse_type(output, "(-> int int int)");
  fprintf(stderr, "Starting: %s\n", "(tuple bool bool bool bool)");
  test_parse_type(output, "(tuple bool bool bool bool)");
  fprintf(stderr, "Starting: %s\n", "(scalar A B C D)");
  test_parse_type(output, "(scalar A B C D)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(scalar X)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "not_a_type");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(bitvector -1929)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(bitvector 0)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(bitvector 321211213456777733887738)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(bitvector 1073741824)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(bitvector 178447/43)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(bitvector 31.4e1)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_type(output, "(bitvector 31.4e-3)");

  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "true");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "false");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "0b30043");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "0b");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "0b00101");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "1/0");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "(/ 1 0)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "(+ 1 2 3 4 5)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "(* 1 2 3 4 5)");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "(not (= 1 (- 5)))");
  fprintf(stderr, "Starting: %s\n", "");
  test_parse_term(output, "(let ((x A) (y B))\n   (= x y))");

  fprintf(stderr, "Starting: %s\n", "");
  show_types(output);
  fprintf(stderr, "Starting: %s\n", "");
  show_terms(output);

  fprintf(stderr, "Done.\n");


  return yices_thread_exit();
}

int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);

    yices_init();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      test_thread(stdout);
    } else {
      launch_threads(nthreads, "test_api3_mt", test_thread);
    }
    

    yices_exit();
  }

  return 0;
}
