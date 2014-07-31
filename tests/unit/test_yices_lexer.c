/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "frontend/yices/yices_lexer.h"

static lexer_t lexer;

static void print_token(token_t tk) {
  printf("---> Token %s\n", yices_token_to_string(tk));
  printf("     pos = %"PRIu64", line = %"PRIu32", column = %"PRIu32"\n",
	 lexer.tk_pos, lexer.tk_line, lexer.tk_column);
  if (tk != TK_LP && tk != TK_RP && tk != TK_EOS && tk != TK_COLON_COLON && tk != TK_ERROR) {
    printf("     value: %s\n", current_token_value(&lexer));
    printf("     length: %"PRIu32"\n", current_token_length(&lexer));
  }
}

int main(int argc, char *argv[]) {
  char *filename;
  token_t tk;

  if (argc <= 1) {
    init_yices_stdin_lexer(&lexer);
  } else {
    filename = argv[1];
    if (init_yices_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(2);
    }
  }

  do {
    tk = next_yices_token(&lexer);
    if (tk >= TK_OPEN_STRING) {
      printf("****** ERROR ******\n");
    }
    print_token(tk);
  } while (tk != TK_EOS);

  close_lexer(&lexer);

  return 0;
}
