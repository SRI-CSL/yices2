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
