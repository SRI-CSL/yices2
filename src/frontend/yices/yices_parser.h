/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parser for the Yices language.
 */

#ifndef __YICES_PARSER_H
#define __YICES_PARSER_H

#include <stdio.h>
#include "parser_utils/parser.h"

/*
 * Three parsing functions.
 *
 * Each function takes an optional output file err as argument.
 * - if err is non-NULL then it must be open/writable and
 *   errors report are written to that file.
 * - if err is NULL then nothing is printed to report errors.
 *   Reports are converted to yices errors, stored in the global
 *   error report record.
 */
// return -1 if there's an error, 0 otherwise
extern int32_t parse_yices_command(parser_t *parser, FILE *err);

// return NULL_TERM if there's an error, the parsed term otherwise
extern term_t parse_yices_term(parser_t *parser, FILE *err);

// return NULL_TYPE if there's an error, the parsed type otherwise
extern type_t parse_yices_type(parser_t *parser, FILE *err);


#endif /* __YICES_PARSER_H */
