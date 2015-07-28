/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR PARSING COMMAND-LINE ARGUMENTS
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include "utils/command_line.h"
#include "utils/string_utils.h"


/*
 * Extract name out of a path as in /usr/bin/name
 * - same as basename
 */

// TODO check whether this works on mingw
#ifdef MINGW
#define PCHAR '\\'
#else
#define PCHAR '/'
#endif

static char *get_basename(char *path) {
  char *s;

  s = strrchr(path, PCHAR);
  if (s != NULL) {
    return s + 1;
  } else {
    return path;
  }
}


/*
 * Initialize parser
 */
void init_cmdline_parser(cmdline_parser_t *p,
                         option_desc_t *options, uint32_t noptions,
                         char **argv, uint32_t argc) {
  p->options = options;
  p->noptions = noptions;
  p->argv = argv;
  p->argc = argc;

  if (argc > 0) {
    p->scan_index = 1;
    p->command_name = get_basename(argv[0]);
  } else {
    p->scan_index = 0;
    p->command_name = NULL;
  }
}


/*
 * Check whether s1 is a prefix of s2
 * If so return a pointer to what follows s1 into s2.
 * If not return NULL.
 */
static char *check_prefix(const char *s1, char *s2) {
  char c1, c2;

  for (;;) {
    c1 = *s1;
    c2 = *s2;
    if (c1 == '\0') return s2;
    if (c1 != c2) return NULL;
    s1 ++;
    s2 ++;
  }
}


/*
 * Search for an option descriptor with abbrev == a
 * - return NULL if not found, a pointer to it otherwise
 * - if a is '\0' just return NULL
 */
static option_desc_t *find_by_abbrev(option_desc_t *options, uint32_t n, char a) {
  uint32_t i;
  option_desc_t *p;

  if (a == '\0') return NULL;

  p = options;
  for (i=0; i<n; i++) {
    if (p->abbrev == a) return p;
    p ++;
  }
  return NULL;
}


/*
 * Search for an option descriptor whose name matches s
 * - matches mean that either s is "name" or s is "name=<value>"
 * - if a match is found, return the corresponding descriptor
 *   and set *value to NULL or to "<value>"
 * - if no match is found, return NULL
 */
static option_desc_t *find_by_name(option_desc_t *options, uint32_t n, char *s, char **value) {
  uint32_t i;
  option_desc_t *p;
  char *q;

  p = options;
  for (i=0; i<n; i++) {
    q = check_prefix(p->name, s);
    if (q != NULL) {
      if (*q == '\0') {
        *value = NULL;
        return p;
      } else if (*q == '=') {
        *value = q + 1;
        return p;
      }
    }
    p ++;
  }
  return NULL;
}



/*
 * Parse e->s_value as an integer argument
 * - convert the value to a 32bit integer and store it in e->i_value
 * - if that fails, set e->status and e->e_code to an error
 * - if that succeeds, set e->status to cmdline_option (i.e., correct option)
 */
static void check_integer_value(cmdline_elem_t *e) {
  int32_t aux;

  assert(e->s_value != NULL);
  switch (parse_as_integer(e->s_value, &aux)) {
  case valid_integer:
    e->status = cmdline_option;
    e->i_value = aux;
    break;

  case integer_overflow:
    e->status = cmdline_error;
    e->i_value = -1;
    e->e_code = cmdline_int_overflow;
    break;

  case invalid_integer:
    e->status = cmdline_error;
    e->i_value = -1;
    e->e_code = cmdline_int_format;
    break;
  }
}


/*
 * Check whether the next component of the command line can
 * be parsed as an integer. If so store it as current value for e.
 */
static void parse_optional_integer(cmdline_parser_t *p, cmdline_elem_t *e) {
  uint32_t i;
  int32_t aux;
  char *s;

  assert(e->s_value == NULL);
  i = p->scan_index;
  if (i < p->argc) {
    s = p->argv[i];
    switch (parse_as_integer(s, &aux)) {
    case valid_integer:
      p->scan_index = i+1;
      e->status = cmdline_option;
      e->s_value = s;
      e->i_value = aux;
      return;

    case integer_overflow:
      p->scan_index = i+1;
      e->status = cmdline_error;
      e->s_value = s;
      e->i_value = -1;
      e->e_code = cmdline_int_overflow;
      return;

    default:
      break;
    }
  }

  // no integer given
  e->i_value = -1;
  e->status = cmdline_option;
}


/*
 * Parse e->s_value as a floating-point argument
 * - convert the value to double and store if in e->d_value
 * - if that fails, set e->status and e->e_code to an error
 * - if that succeeds, set e->status to cmdline_option (i.e., correct option)
 */
static void check_double_value(cmdline_elem_t *e) {
  double aux;

  assert(e->s_value != NULL);
  switch (parse_as_double(e->s_value, &aux)) {
  case valid_double:
    e->status = cmdline_option;
    e->d_value = aux;
    break;

  case double_overflow:
    e->status = cmdline_error;
    e->d_value = -1.0;
    e->e_code = cmdline_float_overflow;
    break;

  case invalid_double:
    e->status = cmdline_error;
    e->d_value = -1.0;
    e->e_code = cmdline_float_format;
    break;
  }
}


/*
 * Check whether the next component of the command line can be parsed
 * as a floating-point number. If so store it as the current value for e.
 */
static void parse_optional_double(cmdline_parser_t *p, cmdline_elem_t *e) {
  uint32_t i;
  double aux;
  char *s;

  assert(e->s_value == NULL);
  i = p->scan_index;
  if (i < p->argc) {
    s = p->argv[i];
    switch (parse_as_double(s, &aux)) {
    case valid_double:
      p->scan_index = i+1;
      e->status = cmdline_option;
      e->s_value = s;
      e->d_value = aux;
      return;

    case double_overflow:
      p->scan_index = i+1;
      e->status = cmdline_error;
      e->s_value = s;
      e->d_value = -1.0;
      e->e_code = cmdline_float_overflow;
      return;

    default:
      break;
    }
  }

  // no number given
  e->d_value = -1.0;
  e->status = cmdline_option;
}


/*
 * Check whether s is a blank string
 */
static bool blank_string(char *s) {
  while (isspace((int) *s)) s++;
  return *s == '\0';
}


/*
 * Check whether e->s_value is a valid string parameter:
 * - whether it's not empty
 */
static void check_string(cmdline_elem_t *e) {
  assert(e->s_value != NULL);

  e->i_value = -1;
  e->status = cmdline_option;
  if (e->s_value[0] == '\0') {
    e->status = cmdline_error;
    e->e_code = cmdline_format;
  }
}


/*
 * Check whether the next component of the command line is
 * a valid string parameter (not empty and does not start with '-')
 * If so, store it as the s_value for e.
 */
static void parse_optional_string(cmdline_parser_t *p, cmdline_elem_t *e) {
  uint32_t i;
  char *s;

  assert(e->s_value == NULL);
  i = p->scan_index;
  if (i < p->argc) {
    s = p->argv[i];
    if (s[0] != '\0' && s[0] != '-') {
      p->scan_index = i + 1;
      e->s_value = s;
    }
  }
  e->status = cmdline_option;
  e->i_value = -1;
}


/*
 * Check whether option with descriptor d has a mandatory or optional parameter
 * and parse the parameter if present.
 * - e->s_value points to the string <value> if the option was given as --option=<value>
 * - e->s_value is NULL if the option was given as -o or --option
 */
static void check_option_parameter(cmdline_parser_t *p, cmdline_elem_t *e,
                                   option_desc_t *d) {
  uint32_t i;

  switch (d->type) {
  case FLAG_OPTION:
    if (e->s_value != NULL) {
      e->status = cmdline_error;
      e->e_code = cmdline_noval_expected;
    } else {
      e->status = cmdline_option;
      e->i_value = -1;
    }
    break;

  case OPTIONAL_INT:
    if (e->s_value != NULL) {
      check_integer_value(e);
    } else {
      parse_optional_integer(p, e);
    }
    break;

  case MANDATORY_INT:
    if (e->s_value == NULL) {
      i = p->scan_index;
      if (i >= p->argc) {
        e->status = cmdline_error;
        e->e_code = cmdline_val_missing;
        return;
      } else {
        e->s_value = p->argv[i];
        p->scan_index = i+1;
      }
    }
    check_integer_value(e);
    break;

  case OPTIONAL_FLOAT:
    if (e->s_value != NULL) {
      check_double_value(e);
    } else {
      parse_optional_double(p, e);
    }
    break;

  case MANDATORY_FLOAT:
    if (e->s_value == NULL) {
      i = p->scan_index;
      if (i >= p->argc) {
        e->status = cmdline_error;
        e->e_code = cmdline_val_missing;
        return;
      } else {
        e->s_value = p->argv[i];
        p->scan_index = i+1;
      }
    }
    check_double_value(e);
    break;

  case OPTIONAL_STRING:
    // reject empty string here
    if (e->s_value != NULL) {
      check_string(e);
    } else {
      parse_optional_string(p, e);
    }
    break;

  case MANDATORY_STRING:
    // accept empty string here
    if (e->s_value == NULL) {
      i = p->scan_index;
      if (i >= p->argc) {
        e->status = cmdline_error;
        e->e_code = cmdline_val_missing;
        return;

      } else {
        e->s_value = p->argv[i];
        p->scan_index = i+1;
      }
    }
    e->status = cmdline_option;
    e->i_value = -1;
    break;


  default:
    assert(false);
  }
}


/*
 * Parse string a as a short option (leading '-' is not included)
 */
static void parse_short_option(cmdline_parser_t *p, cmdline_elem_t *e, char *a) {
  option_desc_t *d;

  if (isalpha((int) a[0]) && a[1] == '\0') {
    e->format = cmdline_short;

    d = find_by_abbrev(p->options, p->noptions, a[0]);
    if (d == NULL) {
      e->status = cmdline_error;
      e->e_code = cmdline_unknown_option;
    } else {
      e->key = d->key;
      e->s_value = NULL;
      check_option_parameter(p, e, d);
    }

  } else {
    e->status = cmdline_error;
    e->e_code = cmdline_format;
  }
}


/*
 * Parse string a as a long option (leading '--' have been removed)
 */
static void parse_long_option(cmdline_parser_t *p, cmdline_elem_t *e, char *a) {
  option_desc_t *d;
  char *suffix;
  uint32_t i;

  e->format = cmdline_long;
  if (a[0] == '\0') {
    // '--' option: interpret the next argument as a generic parameter
    i = p->scan_index;
    if (i < p->argc) {
      e->status = cmdline_argument;
      e->arg = p->argv[i];
      p->scan_index = i+1;
    } else {
      e->status = cmdline_error;
      e->e_code = cmdline_arg_missing;
    }

  } else if (isalpha((int) a[0])) {
    d = find_by_name(p->options, p->noptions, a, &suffix);

    if (d == NULL) {
      e->status = cmdline_error;
      e->e_code = cmdline_unknown_option;
    } else {
      e->key = d->key;
      e->s_value = suffix;

      if (suffix != NULL) {
        e->format = cmdline_long_val;
        if (blank_string(suffix)) {
          e->status = cmdline_error;
          e->e_code = cmdline_format;
          return;
        }
      }

      check_option_parameter(p, e, d);
    }

  } else {
    e->status = cmdline_error;
    e->e_code = cmdline_format;
  }
}


/*
 * Top-level parsing function: fill-in e
 */
void cmdline_parse_element(cmdline_parser_t *p, cmdline_elem_t *e) {
  uint32_t i;
  char *a;

  i = p->scan_index;
  if (i >= p->argc) {
    e->status = cmdline_done;
    return;
  }

  p->scan_index = i+1;
  a = p->argv[i];
  e->arg = a;

  if (*a == '-') {
    a ++;
    if (*a == '-') {
      a ++;
      parse_long_option(p, e, a);
    } else {
      parse_short_option(p, e, a);
    }
  } else {
    e->status = cmdline_argument;
  }
}




/*
 * Print long name or abbreviation of an option based on e->arg
 * - i.e., print e->arg until '=' or '\0' is found.
 */
static void print_option_name(FILE *f, cmdline_elem_t *e) {
  char *s, c;

  s = e->arg;
  c = *s ++;
  while (c != '=' && c != '\0') {
    fputc(c, f);
    c = *s ++;
  }
}


/*
 * Print an error message on stderr
 */
void cmdline_print_error(cmdline_parser_t *p, cmdline_elem_t *e) {
  assert(e->status == cmdline_error);

  if (p->command_name != NULL) {
    fprintf(stderr, "%s: ", p->command_name);
  }

  switch (e->e_code) {
  case cmdline_unknown_option:
    fprintf(stderr, "invalid option: %s\n", e->arg);
    break;

  case cmdline_noval_expected:
    fputs("option ", stderr);
    print_option_name(stderr, e);
    fputs(" takes no parameter\n", stderr);
    break;

  case cmdline_val_missing:
    fputs("option ", stderr);
    print_option_name(stderr, e);
    fputs(" requires an argument\n", stderr);
    break;

  case cmdline_format:
    fprintf(stderr, "invalid option: %s\n", e->arg);
    break;

  case cmdline_int_format:
    if (e->format == cmdline_long_val) {
      fprintf(stderr, "invalid option: %s (parameter must be an integer)\n", e->arg);
    } else {
      fprintf(stderr, "invalid parameter to %s (parameter must be an integer)\n", e->arg);
    }
    break;

  case cmdline_int_overflow:
    if (e->format == cmdline_long_val) {
      fprintf(stderr, "integer overflow: %s\n", e->arg);
    } else {
      fprintf(stderr, "integer overflow: %s %s\n", e->arg, e->s_value);
    }
    break;

  case cmdline_float_format:
    if (e->format == cmdline_long_val) {
      fprintf(stderr, "invalid option: %s (parameter must be a number)\n", e->arg);
    } else {
      fprintf(stderr, "invalid parameter to %s (parameter must be a number)\n", e->arg);
    }
    break;

  case cmdline_float_overflow:
    if (e->format == cmdline_long_val) {
      fprintf(stderr, "floating-point over/underflow: %s\n", e->arg);
    } else {
      fprintf(stderr, "floating-point over/underflow: %s %s\n", e->arg, e->s_value);
    }
    break;

  case cmdline_arg_missing:
    fputs("missing argument after '--'\n", stderr);
    break;

  default:
    assert(false);
  }
}




/*
 * Invalid option argument.
 */
void cmdline_invalid_argument(cmdline_parser_t *p, cmdline_elem_t *e, char *explanation) {
  if (e->format == cmdline_long_val) {
    fprintf(stderr, "invalid option: %s (%s)\n", e->arg, explanation);
  } else {
    fprintf(stderr, "invalid parameter to %s (%s)\n", e->arg, explanation);
  }
}
