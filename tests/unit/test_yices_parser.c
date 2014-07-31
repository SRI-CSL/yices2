/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "utils/memsize.h"
#include "utils/command_line.h"

#include "api/yices_globals.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "parser_utils/term_stack2.h"
#include "frontend/yices/yices_lexer.h"
#include "frontend/yices/yices_parser.h"
#include "yices.h"
#include "yices_exit_codes.h"


/*
 * Command-line flags
 */
enum {
  version_flag,
  help_flag,
  set_dump,
};

#define NUM_OPTIONS (set_dump+1)

static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, version_flag },
  { "help", 'h', FLAG_OPTION, help_flag },
  { "dump", 'd', OPTIONAL_STRING, set_dump },
};


/*
 * Base options
 */
static void print_version(void) {
  printf("Test Yices Parser 2.0 prototype. Copyright SRI International, 2007\n"
	 "GMP %s. Copyright Free Software Foundation, Inc.\n", gmp_version);
  fflush(stdout);
}

static void print_help(char *progname) {
  printf("Usage: %s [options] filename\n", progname);
  printf("Options:\n"
	 "  --version, -V           Display version and exit\n"
	 "  --help, -h              Display this information\n"
	 "  --dump <file>           Dump all internal tables into the given <file>\n"
	 "    or -d <file>          or to stdout if no <file> is given\n"
	 "\n"
	 "For bug reporting and other information, please see http://yices.csl.sri.com/\n");
  fflush(stdout);
}

static void print_usage(char *progname) {
  fprintf(stderr, "Usage: %s [options] <input_file>\n", progname);
  fprintf(stderr, "Try '%s --help' for more information\n", progname);
}


/*
 * Processing of the command-line flags
 * - set the global variables input_filename and dump_filename, and dump_requested
 * - input_filename = NULL means read from stdin
 * - dump_requested = false means don't dump on exit
 * - dump_requested = true means print all internal tables into dump_filename
 *   or, if dump_filename = NULL, print on stdout
 */
static char *input_filename;
static char *dump_filename;
static bool dump_requested;

static void process_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;

  input_filename = NULL;
  dump_filename = NULL;
  dump_requested = false;

  init_cmdline_parser(&parser, options, NUM_OPTIONS, argv, argc);

  for (;;) {
    cmdline_parse_element(&parser, &elem);
    switch (elem.status) {
    case cmdline_done:
      goto done;

    case cmdline_argument:
      if (input_filename == NULL) {
	input_filename = elem.arg;
      } else {
	fprintf(stderr, "%s: can't have several input files\n", parser.command_name);
	goto bad_usage;
      }
      break;

    case cmdline_option:
      switch (elem.key) {
      case version_flag:
	print_version();
	goto quick_exit;

      case help_flag:
	print_help(parser.command_name);
	goto quick_exit;

      case set_dump:
	dump_requested = true;
	if (elem.s_value != NULL) {
	  if (dump_filename == NULL) {
	    dump_filename = elem.s_value;
	  } else {
	    fprintf(stderr, "%s: can't have several dump files\n", parser.command_name);
	    goto bad_usage;
	  }
	}
	break;

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

 quick_exit:
  exit(YICES_EXIT_SUCCESS);

 bad_usage:
  print_usage(parser.command_name);
  exit(YICES_EXIT_USAGE);

 done:
  return;
}




static lexer_t lexer;
static parser_t parser;
static tstack_t stack;

int main(int argc, char *argv[]) {
  bool interactive;
  int32_t code;
  FILE *dump;
  double memused;

  process_command_line(argc, argv);

  yices_init();
  init_tstack(&stack, NUM_BASE_OPCODES);
  interactive = false;

  if (input_filename == NULL) {
    init_yices_stdin_lexer(&lexer);
    interactive = true;
  } else {
    if (init_yices_file_lexer(&lexer, input_filename) < 0) {
      perror(input_filename);
      exit(YICES_EXIT_FILE_NOT_FOUND);
    }
  }

  init_parser(&parser, &lexer, &stack);
  while (current_token(&lexer) != TK_EOS) {
    if (interactive) {
      printf("yices> ");
      fflush(stdout);
    }
    code = parse_yices_command(&parser, stderr);
    if (code < 0) {
      flush_lexer(&lexer);
    }
  }

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);

  memused = mem_size() / (1024 * 1024);
  if (memused > 0) {
    fprintf(stderr, "Memory used: %.2f MB\n", memused);
  }

  if (dump_requested) {
    if (dump_filename == NULL) {
      dump = stdout;
    } else {
      dump = fopen(dump_filename, "w");
      if (dump == NULL) {
	perror(dump_filename);
	exit(YICES_EXIT_FILE_NOT_FOUND);
      }
    }

    fprintf(dump, "\n==== ALL TYPES ====\n");
    print_type_table(dump, __yices_globals.types);
    fflush(dump);
    fprintf(dump, "\n==== ALL TERMS ====\n");
    print_term_table(dump, __yices_globals.terms);
    fflush(dump);

    if (dump_filename != NULL) {
      if (fclose(dump) != 0) {
	fprintf(stderr, "Error while closing dump file: ");
	perror(dump_filename);
      }
    }
  }

  yices_exit();

  return 0;
}
