/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
