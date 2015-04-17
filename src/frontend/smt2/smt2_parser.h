/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parser for the SMT-LIB 2 language.
 */

#ifndef __SMT2_PARSER_H
#define __SMT2_PARSER_H

#include <stdio.h>

#include "parser_utils/parser.h"

/*
 * Parse a command in the SMT-LIB language
 * - return -1 if there's an error, 0 otherwise
 */
extern int32_t parse_smt2_command(parser_t *parser);

#endif /* __SMT2_PARSER_H */
