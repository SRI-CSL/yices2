#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "smt2_lexer.h"

static lexer_t lexer;

static void print_token(smt2_token_t tk) {
  uint32_t n;
  char *s;

  printf("---> Token %s (%"PRId32")\n", smt2_token_to_string(tk), tk);
  printf("     pos = %"PRIu64", line = %"PRIu32", column = %"PRIu32"\n", 
	 lexer.tk_pos, lexer.tk_line, lexer.tk_column);
  n = current_token_length(&lexer);
  s = current_token_value(&lexer);
  printf("     value: %s\n", s);
  printf("     length: %"PRIu32"\n", n);
}

int main(int argc, char *argv[]) {
  char *filename;
  token_t tk;

  if (argc <= 1) {
    init_smt2_stdin_lexer(&lexer);
  } else {
    filename = argv[1];
    if (init_smt2_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(2);
    }
  }

  do {
    tk = next_smt2_token(&lexer);
    if (tk >= SMT2_TK_INVALID_STRING) {
      printf("*** Error ***\n");
    }
    print_token(tk);
  } while (tk != SMT2_TK_EOS);

  close_lexer(&lexer);

  return 0;
}
