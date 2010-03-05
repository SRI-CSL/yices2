/*
 * Parser for the Yices language.
 */

#ifndef __YICES_PARSER_H
#define __YICES_PARSER_H

#include "parser.h"


/*
 * Three parsing functions for now
 */
// return -1 if there's an error, 0 otherwise
extern int32_t parse_yices_command(parser_t *parser);

// return NULL_TERM if there's an error, the parsed term otherwise
extern term_t parse_yices_term(parser_t *parser);

// return NULL_TYPE if there's an error, the parsed type otherwise
extern type_t parse_yices_type(parser_t *parser);


#endif /* __YICES_PARSER_H */
