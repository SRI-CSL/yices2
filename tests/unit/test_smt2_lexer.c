/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>

#include "frontend/smt2/smt2_lexer.h"
#include "utils/command_line.h"
#include "include/yices_exit_codes.h"

static lexer_t lexer;

static void print_token(smt2_token_t tk) {
  smt2_keyword_t kw;
  smt2_symbol_t sym;
  uint32_t n;
  char *s;

  printf("---> Token %s (%"PRId32")\n", smt2_token_to_string(tk), tk);
  printf("     pos = %"PRIu64", line = %"PRIu32", column = %"PRIu32"\n",
	 lexer.tk_pos, lexer.tk_line, lexer.tk_column);
  n = current_token_length(&lexer);
  s = current_token_value(&lexer);
  if (tk != SMT2_TK_LP && tk != SMT2_TK_RP && tk != SMT2_TK_ERROR && tk != SMT2_TK_EOS) {
    printf("     value: '%s'\n", s);
    printf("     length: %"PRIu32"\n", n);
  }

  if (tk == SMT2_TK_KEYWORD) {
    kw = smt2_string_to_keyword(s, n);
    printf("      keyword %"PRId32": %s\n", kw, smt2_keyword_to_string(kw));
  } else if (tk == SMT2_TK_SYMBOL) {
    sym = smt2_string_to_symbol(s, n);
    printf("      symbol %"PRId32": %s\n", sym, smt2_symbol_to_string(sym));
  }

}



/*
 * Global variables: input file + logic name
 */
static char *filename;
static char *logic_name;
static smt_logic_t logic_code;


/*
 * Command-line option: to select the logic
 */
typedef enum optid {
  logic_option, // logic
  help_flag,    // print help and exit
} optid_t;

#define NUM_OPTIONS (help_flag+1)

static option_desc_t options[NUM_OPTIONS] = {
  { "logic", '\0', MANDATORY_STRING, logic_option },
  { "help", 'h', FLAG_OPTION, help_flag },
};

static void print_help(char *progname) {
  printf("Usage: %s [options] <optional filename>\n\n", progname);
  printf("Options:\n"
	 "  --help, -h            Display this information\n"
	 "  --logic=name          Select an SMT-LIB logic (e.g., QF_UFLIA)\n"
	 "\n");
  fflush(stdout);
}

static void print_usage(char *progname) {
  fprintf(stderr, "Try '%s --help' for more information\n", progname);
}

/*
 * Proces the command line options
 * - set filename and logic_code if they are given
 */
static void process_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;

  filename = NULL;
  logic_name = NULL;
  logic_code = SMT_UNKNOWN;

  init_cmdline_parser(&parser, options, NUM_OPTIONS, argv, argc);

  for (;;) {
    cmdline_parse_element(&parser, &elem);
    switch (elem.status) {
    case cmdline_done:
      goto done;

    case cmdline_argument:
      if (filename == NULL) {
	filename = elem.arg;
      } else {
	fprintf(stderr, "%s: can't have several input files\n", parser.command_name);
	goto bad_usage;
      }
      break;

    case cmdline_option:
      switch (elem.key) {
      case logic_option:
	if (logic_name == NULL) {
	  logic_name = elem.s_value;
	  logic_code = smt_logic_code(logic_name);
	  if (logic_code == SMT_UNKNOWN) {
	    fprintf(stderr, "%s: unkknown logic %s\n", parser.command_name, logic_name);
	    goto bad_usage;
	  }
	} else if (strcmp(logic_name, elem.s_value) != 0) {
	  fprintf(stderr, "%s: only one logic can be speicifed\n", parser.command_name);
	  goto bad_usage;
	}
	break;

      case help_flag:
	print_help(parser.command_name);
	goto quick_exit;

      default:
	assert(false);
	break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      goto bad_usage;
    }
  }

 done:
  return;

 quick_exit:
  exit(YICES_EXIT_SUCCESS);

 bad_usage:
  print_usage(parser.command_name);
  exit(YICES_EXIT_USAGE);
}


int main(int argc, char *argv[]) {
  token_t tk;

  process_command_line(argc, argv);

  if (filename == NULL) {
    init_smt2_stdin_lexer(&lexer);
  } else if (init_smt2_file_lexer(&lexer, filename) < 0) {
    perror(filename);
    exit(YICES_EXIT_FILE_NOT_FOUND);
  }

  if (logic_code != SMT_UNKNOWN) {
    smt2_lexer_activate_logic(logic_code);
    printf("Activating symbols for logic %s\n", logic_name);
    fflush(stdout);
  }

  do {
    tk = next_smt2_token(&lexer);
    if (tk >= SMT2_TK_INVALID_STRING) {
      printf("*** Error ***\n");
    }
    print_token(tk);
  } while (tk != SMT2_TK_EOS);

  close_lexer(&lexer);

  return 0;
}
