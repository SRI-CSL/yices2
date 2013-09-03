/*
 * Yices solver: input in the SMT-LIB 2.0 language
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>

#include "cputime.h"
#include "memsize.h"
#include "command_line.h"

#include "smt2_lexer.h"
#include "smt2_parser.h"
#include "smt2_term_stack.h"
#include "smt2_commands.h"

#include "yices.h"
#include "yices_exit_codes.h"


/*
 * Global objects:
 * - lexer/parser/stack: for processing the SMT2 input
 * - incremental: if this flag is true, support for push/pop
 *   and multiple check_sat is enabled. Otherwise, the solver
 *   is configured to handle a set of declarations/assertions
 *   followed by a single call to (check_sat).
 * - filename = name of the input file (NULL means read stdin)
 */
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;

static bool incremental;
static char *filename;


/****************************
 *  COMMAND-LINE ARGUMENTS  *
 ***************************/

typedef enum optid {
  show_version_opt,     // print version and exit
  show_help_opt,        // print help and exit
  incremental_opt,      // enable incremental mode
} optid_t;

#define NUM_OPTIONS (incremental_opt+1)

/*
 * Option descriptors
 */
static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, show_version_opt },
  { "help", 'h', FLAG_OPTION, show_help_opt },
  { "incremental", 'i', FLAG_OPTION, incremental_opt },
};


/*
 * Processing of command-line
 */
static void print_version(void) {
  printf("Yices %s. Copyright SRI International.\n"
         "GMP %s. Copyright Free Software Foundation, Inc.\n"
         "Build date: %s\n"
         "Platform: %s (%s)\n",
         yices_version, gmp_version, 
         yices_build_date, yices_build_arch, yices_build_mode);
  fflush(stdout);
}

static void print_help(const char *progname) {
  printf("Usage: %s [option] filename\n", progname);
  printf("Option summary:\n"
	 "    --version, -V           Show version and exit\n"
	 "    --help, -h              Print this message and exit\n"
	 "    --incremental, -i       Enable support for push/pop\n"
	 "\n"
	 "For bug reports and ohter information, please see http://yices.csl.sri.com/\n");
  fflush(stdout);
}

/*
 * Message for unrecognized options or other errors on the command line.
 */
static void print_usage(const char *progname) {
  fprintf(stderr, "Usage: %s [options] filename\n", progname);
  fprintf(stderr, "Try '%s --help' for more information\n", progname);  
}


/*
 * Parse the command line and process options
 */
static void parse_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;
  optid_t k;

  filename = NULL;
  incremental = false;

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
	fprintf(stderr, "%s: too many arguments\n", parser.command_name);
	print_usage(parser.command_name);
	exit(YICES_EXIT_USAGE);
      }
      break;

    case cmdline_option:
      k = elem.key;
      switch (k) {
      case show_version_opt:
	print_version();
	exit(YICES_EXIT_SUCCESS);

      case show_help_opt:
	print_help(parser.command_name);
	exit(YICES_EXIT_SUCCESS);

      case incremental_opt:
	incremental = true;
	break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      fprintf(stderr, "Try %s --help for more information\n", parser.command_name);
      exit(YICES_EXIT_USAGE);
    }
  }

 done: // nothing special to do
  return; 
}


int main(int argc, char *argv[]) {
  int32_t code;
  double time, mem_used;

  parse_command_line(argc, argv);

  if (filename != NULL) {
    // read from file
    if (init_smt2_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(YICES_EXIT_FILE_NOT_FOUND);
    }
  } else {
    // read from stdin
    init_smt2_stdin_lexer(&lexer);
  }

  yices_init();
  init_smt2(!incremental);
  init_smt2_tstack(&stack);
  init_parser(&parser, &lexer, &stack);

  while (smt2_active()) {
    code = parse_smt2_command(&parser);
    if (code < 0) {
      // syntax error
      if (filename == NULL) { // ?? not sure that makes sense
	flush_lexer(&lexer); 
      } else {
	break; // exit
      }
      fflush(stdout);
      break;
    }
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

