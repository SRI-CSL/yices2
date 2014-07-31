/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the command line parser
 */

#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/command_line.h"

enum option_keys {
  TEST1,
  TEST2,
  TEST3,
  TEST4,
  TEST5,
  TEST6,
};

static option_desc_t options[6] = {
  { "flag", 't', FLAG_OPTION, TEST1 },
  { "flag-trick", 'u', FLAG_OPTION, TEST2 },
  { "int-required", 'i', MANDATORY_INT, TEST3 },
  { "int-optional", 'j', OPTIONAL_INT, TEST4 },
  { "string-required", 's', MANDATORY_STRING, TEST5 },
  { "string-optional", 'w', OPTIONAL_STRING, TEST6 },
};


static void show_cmdline_details(cmdline_elem_t *e) {
  printf("  option given as %s\n", e->arg);
  switch (e->format) {
  case cmdline_short:
    printf("  short name\n");
    break;
  case cmdline_long:
    printf("  long name\n");
    break;
  case cmdline_long_val:
    printf("  long name + value\n");
    break;
  default:
    printf("   unknown format\n");
    break;
  }
  if (e->s_value == NULL) {
    printf("  no parameter\n");
  } else {
    printf("  parameter %s (i_value = %"PRId32")\n", e->s_value, e->i_value);
  }
}

static void show_cmdline_error(cmdline_elem_t *e) {
  switch (e->e_code) {
  case cmdline_unknown_option:
    printf("  unrecognized option %s\n", e->arg);
    break;
  case cmdline_noval_expected:
    printf("  option %s requires no argument\n", e->arg);
    break;
  case cmdline_val_missing:
    printf("  option %s requires an argument\n", e->arg);
    break;
  case cmdline_format:
    printf("  invalid option %s\n", e->arg);
    break;
  case cmdline_int_format:
    printf("  value %s is not an integer\n", e->s_value);
    break;
  case cmdline_int_overflow:
    printf("  cannot deal with value %s: overflow\n", e->s_value);
    break;
  case cmdline_arg_missing:
    printf("  -- must be followed by a parameter\n");
    break;
  default:
    printf("  unknown error code\n");
    break;
  }
}

static void show_cmdline_element(cmdline_elem_t *e, uint32_t i) {
  int32_t k;

  printf("option[%"PRId32"]: ", i);
  switch (e->status) {
  case cmdline_done:
    printf("end\n");
    break;

  case cmdline_argument:
    printf("string argument: %s\n", e->arg);
    break;

  case cmdline_option:
    k = e->key;
    printf("option %s\n", options[k].name);
    show_cmdline_details(e);
    break;

  case cmdline_error:
    printf("parse error\n");
    show_cmdline_details(e);
    show_cmdline_error(e);
    break;

  default:
    printf("invalid status\n");
    break;
  }
}


int main(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;
  uint32_t i;

  init_cmdline_parser(&parser, options, 6, argv, argc);

  i = 0;
  for (;;) {
    elem.s_value = NULL;
    cmdline_parse_element(&parser, &elem);
    show_cmdline_element(&elem, i);
    if (elem.status == cmdline_done) break;
    if (elem.status == cmdline_error) {
      cmdline_print_error(&parser, &elem);
      break;
    }
    i ++;
  }

  return 0;
}
