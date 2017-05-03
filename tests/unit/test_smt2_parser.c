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
#include <stdbool.h>
#include <inttypes.h>

#include "frontend/smt2/smt2_commands.h"
#include "frontend/smt2/smt2_lexer.h"
#include "frontend/smt2/smt2_parser.h"
#include "frontend/smt2/smt2_term_stack.h"
#include "parser_utils/tstack_internals.h"
#include "utils/cputime.h"
#include "utils/memsize.h"

#include "yices.h"
#include "yices_exit_codes.h"


/*
 * Replacement for check_sat/push/pop/get_value:
 * - do nothing
 */
static void check_smt2_skip(tstack_t *stack, stack_elem_t *f, uint32_t n) {
}

static void eval_smt2_skip(tstack_t *stack, stack_elem_t *f, uint32_t n) {
  tstack_pop_frame(stack);
  no_result(stack);
}


static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static bool interactive;

int main(int argc, char *argv[]) {
  char *filename;
  int32_t code;
  double time, mem_used;

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
  init_smt2(true, 0, interactive);
  init_smt2_tstack(&stack);
  init_parser(&parser, &lexer, &stack);

  // disable SMT2_CHECK_SAT/PUSH/POP/GET_VALUE
  tstack_add_op(&stack, SMT2_CHECK_SAT, false, eval_smt2_skip, check_smt2_skip);
  tstack_add_op(&stack, SMT2_PUSH, false, eval_smt2_skip, check_smt2_skip);
  tstack_add_op(&stack, SMT2_POP, false, eval_smt2_skip, check_smt2_skip);
  tstack_add_op(&stack, SMT2_GET_VALUE, false, eval_smt2_skip, check_smt2_skip);

  //  smt2_set_verbosity(100);

  while (smt2_active()) {
    if (interactive) {
      fputs("smt2> ", stdout);
      fflush(stdout);
    }
    code = parse_smt2_command(&parser);
    if (code < 0) {
      // syntax error
      if (interactive) {
	flush_lexer(&lexer);
      } else {
	break; // exit
      }
    }
    fflush(stdout);
  }

  // statistics
  time = get_cpu_time();
  mem_used = mem_size() / (1024 * 1024);
  printf("\nRun time: %.4f s\n", time);
  printf("Memory used: %.2f MB\n\n", mem_used);
  fflush(stdout);

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);
  delete_smt2();
  yices_exit();

  return YICES_EXIT_SUCCESS;
}

