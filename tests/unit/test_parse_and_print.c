/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * FOR TESTING OF THE PRETTY PRINTER
 *
 * Parse a benchmark in the SMT-LIB notation, then display the
 * assertions using the pretty printer.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>


#include "utils/cputime.h"
#include "utils/memsize.h"

#include "api/yices_globals.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_parser.h"
#include "frontend/smt1/smt_term_stack.h"
#include "yices.h"
#include "yices_exit_codes.h"


static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;


/*
 * To compute the area offset:
 * - the last assertion will be displayed after
 *   "Assertion[n-1]:  "
 * - so the left margin is strlen("Assertion[]:  ") + the number of digits in n-1
 */
static uint32_t left_margin(uint32_t n) {
  uint32_t k, i;

  i = 1;
  k = 10;
  while (n > k) {
    i++;
    k *= 10;
  }
  return i + 14;
}


/*
 * Print spaces to align assertions
 * - n = total number of assertions
 * - i = current assertion
 *
 * This adds enough spaces after 'Assertion[i]:'
 * to make sure that 'Assertion[i]:' and 'Assertion[n-1]:'
 * are aligned.
 *
 * Example: if n = 200, then 'Assertion[199]:' takes
 * 2 more characters than 'Assertion[2]' so
 * print_space(2, 200) should print two spaces to compensate
 */
static void print_space(uint32_t i, uint32_t n) {
  uint32_t k;

  k = 10;
  while (i >= k) {
    k *= 10;
  }
  while (n > k) {
    fputc(' ', stdout);
    k *= 10;
  }
}



int main(int argc, char *argv[]) {
  pp_area_t area;
  char *filename;
  int32_t code;
  double time, mem_used;
  uint32_t i, n;

  if (argc > 2) {
    fprintf(stderr, "Usage: %s <filename>\n", argv[0]);
    exit(YICES_EXIT_USAGE);
  }

  if (argc == 2) {
    // read from file
    filename = argv[1];
    if (init_smt_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(YICES_EXIT_FILE_NOT_FOUND);
    }
  } else {
    // read from stdin
    init_smt_stdin_lexer(&lexer);
  }

  yices_init();
  init_smt_tstack(&stack);

  init_parser(&parser, &lexer, &stack);
  init_benchmark(&bench);
  code = parse_smt_benchmark(&parser, &bench);
  if (code == 0) {
    printf("No syntax error found\n");
  }

  time = get_cpu_time();
  mem_used = mem_size() / (1024 * 1024);
  printf("Construction time: %.4f s\n", time);
  printf("Memory used: %.2f MB\n\n", mem_used);
  fflush(stdout);

  // TEST PRETTY PRINTER HERE
  n = bench.nformulas;
  area.width = 160;
  area.height = 10000;
  area.offset = left_margin(n);
  area.stretch = false;
  area.truncate = true;
  printf("Benchmark: %s\n", bench.name);
  printf("Logic: %s\n", bench.logic_name);
  printf("%"PRIu32" assertions\n\n", bench.nformulas);
  fflush(stdout);

  for (i=0; i<n; i++) {
    printf("Assertion[%"PRIu32"]:  ", i);
    print_space(i, n);
    pretty_print_term_full(stdout, &area, __yices_globals.terms, bench.formulas[i]);
  }


  delete_benchmark(&bench);
  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);
  yices_exit();

  return YICES_EXIT_SUCCESS;
}


