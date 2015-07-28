/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parsing of command-line arguments follows more or less the GNU
 * style. Options have a long name of the form --option and,
 * optionally, an abbreviation of the from -o where o is a single
 * character.
 *
 * The argument <value> to an option can be given as
 *   --option=<value>
 *   --option <value>
 *   -o <value>
 * For options with no parameter, the allowed forms are --option or -o
 *
 * Multiple short-name options must be separated. The form -abc
 * is not supported; it must be written -a -b -c.
 *
 * Options can be of different types, which determine whether
 * an argument is required or allowed, and how the argument is parsed.
 *
 * For options with an optional value, the parser uses the following
 * conventions.
 * --option=<value>   no ambiguity, <value> is parsed as is
 *
 * --option <next>    if <next> does not start with '-' it's
 * -o <next>          taken as <value>. If <next> starts with '-'
 *                    and can be parsed as an integer and option
 *                    has integer type, it's also taken as <value>
 *
 * For options with mandatory argument, anything that follows
 * --option or -o is taken as the argument.
 *
 * Any string that's not an option argument and does not start with
 * '-' is considered as a generic string parameter. Any string that follows
 * '--' (even if it starts with '-') is also considered a string
 * argument.
 */

#ifndef __COMMAND_LINE_H
#define __COMMAND_LINE_H

#include <stdint.h>
#include <stdbool.h>


/*
 * Option types
 */
typedef enum option_type {
  FLAG_OPTION,      // no argument
  OPTIONAL_INT,     // an optional integer argument
  MANDATORY_INT,    // a required integer argument
  OPTIONAL_FLOAT,   // an optional floating-point argument
  MANDATORY_FLOAT,  // a required floating-point argument
  OPTIONAL_STRING,  // optional string
  MANDATORY_STRING, // required string argument
} option_type_t;


/*
 * Option descriptor:
 * - name must be the long name, without prefix '--'
 * - abbrev is a one-character abbreviation
 * - set abbrev to a non alpha character (e.g., '\0') if there's
 *   no abbreviation.
 * - type must be one of the above types
 * - key is the option id
 */
typedef struct option_desc_s {
  const char *name;
  char abbrev;
  uint8_t type;
  uint16_t key;
} option_desc_t;


/*
 * Results from parsing are stored into a cmdline_elem_t structure:
 * - status = parsing result
 * - format = what format was seen
 * - arg = argument or option name being parsed
 * - key = option id
 * - s_val = string value
 * - i_val = integer value
 * - d_val = floating-point value (double)
 * - e_code = error code
 */
typedef struct cmdline_elem_s {
  uint8_t status;
  uint8_t format;
  uint16_t key;
  uint32_t e_code;
  int32_t i_value;
  double d_value;
  char *s_value;
  char *arg;
} cmdline_elem_t;


/*
 * Status + substatus + error codes
 */
enum cmd_line_status {
  cmdline_done,     // all arguments have been processed
  cmdline_argument, // generic argument
  cmdline_option,   // valid option
  cmdline_error,    // incorrect option
};

enum cmdline_format {
  cmdline_short,    // -o
  cmdline_long,     // --option
  cmdline_long_val, // --option=<value>
};

enum cmdline_error {
  cmdline_unknown_option,  // -x or --xxx when x is not recognized
  cmdline_noval_expected,  // option needs no argument, one was given (i.e., --flag=<value>)
  cmdline_val_missing,     // option has a mandatory argument, none was given
  cmdline_format,          // something like --xxx= or -xx or -2
  cmdline_int_format,      // value was given but could not be parsed as an integer
  cmdline_int_overflow,    // integer value was given but does not fit in 32bits
  cmdline_float_format,    // value was given but could not be parsed as a double
  cmdline_float_overflow,  // underflow/overflow value
  cmdline_arg_missing,     // nothing after '--'
};


/*
 * Parser structure:
 * - options = array of option descriptors
 * - noptions = size of that array
 * - argv = array of string (command line arguments)
 * - argc = size of that array
 * - scan_index = pointer to the next argv to examine
 * - command_name = argv[0]
 */
typedef struct cmdline_parser_s {
  option_desc_t *options;
  char **argv;
  char *command_name;
  uint32_t noptions;
  uint32_t argc;
  uint32_t scan_index;
} cmdline_parser_t;



/*
 * Initialize parser structure for the
 * given options and command-line arguments
 */
extern void init_cmdline_parser(cmdline_parser_t *p,
                                option_desc_t *options, uint32_t noptions,
                                char **argv, uint32_t argc);


/*
 * Fill-in e with the next option or command line element.
 * Increment p->scan_index to point to whatever follows.
 */
extern void cmdline_parse_element(cmdline_parser_t *p, cmdline_elem_t *e);


/*
 * Print a default error message based on e's content
 * e->status must be cmdline_error
 */
extern void cmdline_print_error(cmdline_parser_t *p, cmdline_elem_t *e);


/*
 * Print a message of the form "invalid option: --x=val (<explanation)>"
 * - use this if the option was parsed correctly, but the parameter <val>
 *   is not valid.
 */
extern void cmdline_invalid_argument(cmdline_parser_t *p, cmdline_elem_t *e, char *explanation);


#endif /* __COMMAND_LINE_H */
