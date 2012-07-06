#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>

#include "cputime.h"
#include "memsize.h"

#include "smt2_lexer.h"
#include "smt2_parser.h"
#include "yices.h"
#include "yices_exit_codes.h"

static lexer_t lexer;
static parser_t parser;
static tstack_t stack;

static bool done;
static bool interactive;

int main(int argc, char *argv[]) {
  char *filename;
  uint32_t good, bad;
  int32_t code;  

  if (argc > 2) {
    fprintf(stderr, "Usage: %s <filename>\n", argv[0]);
    exit(YICES_EXIT_USAGE);
  }

  if (argc == 2) {
    // read from file
    interactive = false;
    filename = argv[1];
    if (init_smt2_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(YICES_EXIT_FILE_NOT_FOUND);
    }
  } else {
    // read from stdin
    interactive = true;
    init_smt2_stdin_lexer(&lexer);
  }

  yices_init();
  tstack_set_smt_mode();
  init_tstack(&stack);
  init_parser(&parser, &lexer, &stack);

  done = false;
  good = 0;
  bad = 0;
  while (current_token(&lexer) != SMT2_TK_EOS && !done) {
    if (interactive) {
      fputs("smt2> ", stdout);
      fflush(stdout);
    }
    code = parse_smt2_command(&parser, stderr);
    if (code < 0) {
      bad ++;
      if (interactive) {
	flush_lexer(&lexer); 
      } else {
	done = true;
      }
    } else {
      good ++;
    }
    fflush(stdout);
  }

  // summarize
  printf("read %"PRIu32" commands (%"PRIu32" errors)\n", good + bad, bad);
  fflush(stdout);

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);
  yices_exit();

  return YICES_EXIT_SUCCESS;
}

