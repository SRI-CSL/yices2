/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EXTENSION OF TERM-STACK: YICES 2 COMMANDS
 */

/*
 * The Yices commands are implemented in yices_reval.c.  We list the
 * opcodes here for use by yices_parser.c and term_stack_errors.c.
 */

#ifndef __YICES_TSTACK_OPS_H
#define __YICES_TSTACK_OPS_H

#include "parser_utils/term_stack2.h"

/*
 * We add two variants of define-term and define-types
 * and the following commands that do not exist in term_stack2.c
 */
enum yices_opcodes {
  DEF_YICES_TYPE = NUM_BASE_OPCODES, // [define-type ...]
  DEF_YICES_TERM,                    // [define ...]
  EXIT_CMD,                          // [exit]
  ASSERT_CMD,                        // [assert <term>]
  CHECK_CMD,                         // [check]
  SHOWMODEL_CMD,                     // [show-model]
  EVAL_CMD,                          // [eval <term>]
  PUSH_CMD,                          // [push]
  POP_CMD,                           // [pop]
  RESET_CMD,                         // [reset]
  ECHO_CMD,                          // [echo <string>]
  INCLUDE_CMD,                       // [include <string>]
  SET_PARAM_CMD,                     // [set-param <symbol> <value> ]
  SHOW_PARAM_CMD,                    // [show-param <symbol> ]
  SHOW_PARAMS_CMD,                   // [show-params]
  SHOW_STATS_CMD,                    // [show-stats]
  RESET_STATS_CMD,                   // [reset-stats]
  SET_TIMEOUT_CMD,                   // [set-timeout <rational>]
  SHOW_TIMEOUT_CMD,                  // [show-timeout]
  HELP_CMD,                          // [help] or [help <symbol>] or [help <string>]
  EFSOLVE_CMD,                       // [ef-solve]
  EXPORT_CMD,                        // [export <string>]
  SHOW_IMPLICANT_CMD,                // [show-implicant]
  DUMP_CMD,                          // [dump]
};


#define NUM_YICES_OPCODES (DUMP_CMD+1)


#endif /* __YICES_TSTACK_OPS_H */
