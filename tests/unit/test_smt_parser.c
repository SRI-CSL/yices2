/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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

static char *status2string[] = {
  "none", "unsat", "sat", "unknown",
};

#if 0
// not used anymore
static void print_benchmark(FILE *f, smt_benchmark_t *bench) {
  uint32_t i, n;

  n = bench->nformulas;
  fprintf(f, "Benchmark %s\n", bench->name);
  fprintf(f, "Logic: %s\n", bench->logic_name);
  fprintf(f, "Parameter: %"PRId32"\n", bench->logic_parameter);
  fprintf(f, "Status: %s\n", status2string[bench->status]);
  fprintf(f, "Number of formulas or assumptions: %"PRIu32"\n", n);

  for (i=0; i<n; i++) {
    fprintf(f, "\n---- Assertion %"PRIu32" ----\n", i);
    print_term(f, bench->formulas[i]);
    fprintf(f, "\n");
  }
}
#endif


/*
 * Temporary test. Check whether one of the input assertion is reduced
 * to false by simplification. This is checked independent of the
 * logic label.
 */
static bool benchmark_reduced_to_false(smt_benchmark_t *bench) {
  uint32_t i, n;
  term_t f;

  n = bench->nformulas;
  for (i=0; i<n; i++) {
    f = bench->formulas[i];
    assert(is_boolean_term(__yices_globals.terms, f));
    if (f == false_term) {
      return true;
    }
  }

  return false;
}


static void dump_benchmark(FILE *f, smt_benchmark_t *bench) {
  uint32_t i, n;

  n = bench->nformulas;
  fprintf(f, "Benchmark %s\n", bench->name);
  fprintf(f, "Logic: %s\n", bench->logic_name);
  fprintf(f, "Parameter: %"PRId32"\n", bench->logic_parameter);
  fprintf(f, "Status: %s\n", status2string[bench->status]);
  fprintf(f, "Number of formulas or assumptions: %"PRIu32"\n", n);
  fprintf(f, "Assertions: ");
  for (i=0; i<n; i++) {
    if (i % 20 == 19) {
      fprintf(f, "\n  ");
    }
    fprintf(f, " ");
    print_term_id(f, bench->formulas[i]);
  }
  fprintf(f, "\n");

  fprintf(f, "\n---- All types ----\n");
  print_type_table(f, __yices_globals.types);

  fprintf(f, "\n\n---- All terms ----\n");
  print_term_table(f, __yices_globals.terms);
  fprintf(f, "\n\n");
  fflush(f);
}


int main(int argc, char *argv[]) {
  char *filename;
  int32_t code;
  FILE *dump;
  double time, mem_used;

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

  if (benchmark_reduced_to_false(&bench)) {
    printf("Reduced to false\n\nunsat\n");
    fflush(stdout);
  }
  printf("\n");

  time = get_cpu_time();
  mem_used = mem_size() / (1024 * 1024);
  printf("Construction time: %.4f s\n", time);
  printf("Memory used: %.2f MB\n\n", mem_used);
  fflush(stdout);

  dump = fopen("yices2new.dmp", "w");
  if (dump == NULL) {
    perror("yices2new.dmp");
  } else {
    dump_benchmark(dump, &bench);
    fclose(dump);
  }

  delete_benchmark(&bench);
  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);
  yices_exit();

  return YICES_EXIT_SUCCESS;
}

