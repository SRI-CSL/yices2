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

#include "frontend/smt1/smt_lexer.h"
#include "terms/bv_constants.h"

static lexer_t lexer;

static uint32_t bitvector[100];

static void print_token(token_t tk) {
  uint32_t n;
  char *s;
  int32_t code;

  printf("---> Token %s\n", smt_token_to_string(tk));
  printf("     pos = %"PRIu64", line = %"PRIu32", column = %"PRIu32"\n",
	 lexer.tk_pos, lexer.tk_line, lexer.tk_column);
  n = current_token_length(&lexer);
  s = current_token_value(&lexer);
  if (n > 0) {
    printf("     value: %s\n", s);
    printf("     length: %"PRIu32"\n", n);
  }

  switch (tk) {
  case SMT_TK_BV_BINCONSTANT:
    if (n < 5) {
      printf("***** ERROR ******\n");
    } else {
      n = n - 5; // remove bvbin prefix
      if (n < 100) {
	code = bvconst_set_from_string(bitvector, n, s + 5);
	if (code < 0) {
	  printf("***** ERROR ******\n");
	} else {
	  printf("     val: ");
	  bvconst_print(stdout, bitvector, n);
	  printf("\n\n");
	}
      }
    }
    break;
  case SMT_TK_BV_HEXCONSTANT:
    if (n < 5) {
      printf("***** ERROR ******\n");
    } else {
      n = n - 5; // remove bvhex prefix and null terminator
      if (n < 100) {
	code = bvconst_set_from_hexa_string(bitvector, n, s + 5);
	if (code < 0) {
	  printf("***** ERROR ******\n");
	} else {
	  printf("     val: ");
	  bvconst_print(stdout, bitvector, 4 * n);
	  printf("\n\n");
	}
      }
    }
    break;
  }
}

int main(int argc, char *argv[]) {
  char *filename;
  token_t tk;

  if (argc <= 1) {
    init_smt_stdin_lexer(&lexer);
  } else {
    filename = argv[1];
    if (init_smt_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(2);
    }
  }

  do {
    tk = next_smt_token(&lexer);
    if (tk >= SMT_TK_OPEN_STRING) {
      printf("*** Error ***\n");
    }
    print_token(tk);
  } while (tk != SMT_TK_EOS);

  close_lexer(&lexer);

  return 0;
}
