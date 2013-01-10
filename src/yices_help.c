/*
 * Help command for Yices
 */

#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#include "memalloc.h"
#include "yices_help.h"


/*
 * Help data:
 * - an array of records
 * - each record consists of five fields
 *    name = a string
 *    category = code
 *    synopsis = a string
 *    short_expl = summary explanation
 *    long_expl = long explanation
 *
 * - long_expl may be NULL
 */

// categories
typedef enum {
  HCOMMAND,     // Yices command
  HTYPE,        // Types and type constructors
  HGENERIC,     // General constructs (apply to all types)
  HBOOLEAN,     // Boolean operators and constants
  HARITHMETIC,  // Arithemtic operators and constants
  HBITVECTOR,   // Bitvector operators
  HPARAM,       // Parameters (in (set-param ...)
  HMISC,        // Everything else
} htype_t;

typedef struct help_record_s {
  char *name;
  htype_t category;
  char *synopsis;
  char *short_expl;
  char *long_expl;
} help_record_t;


static const help_record_t help_data[] = {
  { "define-type", HCOMMAND, 
    "(define-type [name])", 
    "Declare a new uninterpreted type called [name]",
    "   [name] must be a fresh name\n" },

  { "define-type", HCOMMAND, 
    "(define-type [name] [typedef])",
    "Declare a new type called [name] equal to the given [typedef]",
    "   [name] must be a fresh name\n"
    "   [typedef] can be\n"
    "      a primitive type: 'bool', 'real', 'int', or '(bitvector k)'\n"
    "      a function type:  '(-> [type] ... [type])'\n"
    "      a tuple type:     '(tuple [type] ... [type])'\n"
    "      a scalar type:    '(scalar [name] .... [name])'\n" },

  { "define", HCOMMAND, 
    "(define [name] :: [type])",
    "Define a new uninterpreted constant of type [type] called [name]",
    "   [name] must be fresh\n" },

  { "define", HCOMMAND, 
    "(define [name] :: [type] [expr])",
    "Introduce a new constant [name] of type [type], equal to [expr]",
    "   [name] must be fresh\n"
    "   [expr] must be an expression of type [type] or a subtype of [type]\n" },

  { "assert", HCOMMAND,
    "(assert [expr])",
    "Add an assertion to the logical context",
    "   [expr] must be a Boolean expression\n" },

  { "check", HCOMMAND, 
    "(check)",
    "Check whether the logical context is satisfiable",
    NULL },

  { "push", HCOMMAND, 
    "(push)", 
    "Start a new assertion scope",
    NULL },

  { "pop", HCOMMAND,
    "(pop)",
    "Remove all assertions added since the matching (push)",
    "This does not remove term or type declarations, only the assertions.\n"},

  { "reset", HCOMMAND, 
    "(reset)", 
    "Reset the logical context (to the empty context)",
    "All assertions are removed, Type and term declarations are kept.\n" },

  { "show-model", HCOMMAND,
    "(show-model)",
    "Show the current model",
    "\n"
    "This command displays the model if one is available, that is,\n"
    "after a call to (check) that returns 'sat' or 'unknown'.\n" },

  { "eval", HCOMMAND, 
    "(eval [expr])",
    "Show the value of [expr] in the current model",
    "\n"
    "This may be used after a call to (check) that returns 'sat' or 'unknown'.\n" },

  { "include", HCOMMAND,
    "(include [filename])",
    "Reads commands from a file",
    "   [filename] must be given as a string as in \"example.ys\"\n" },

  { "echo", HCOMMAND,
    "(echo [string])",
    "Output [string]",
    NULL },

  { "set-param", HCOMMAND, 
    "(set-param [name] [value])",
    "Set a parameter",
    "   [name] must be a parameter name\n"
    "   [value] must be an immediate value (i.e., a number, Boolean, or symbol)\n"
    "\n"
    "Parameters control the preprocessing, simplification, and search\n"
    "heuristics used by Yices. Type '(help params)' to see the list of\n"
    "all parameters.\n" },

  { "show-param", HCOMMAND, "(show-param [name])",
    "Show the value of parameter [name]",
    "\n"
    "Type '(help params)' to see the list of all parameters.\n" },

  { "show-params", HCOMMAND, "(show-params)",
    "Show all parameters and their current value",
    NULL },

  { "show-stats", HCOMMAND, "(show-stats)",
    "Show statistics",
    NULL},

  { "reset-stats", HCOMMAND, "(reset-stats)",
    "Reset the statistics counters",
    NULL },

  { "set-timeout", HCOMMAND, "(set-timeout [value])",
    "Give a timeout",
    "   [value] must be a non-negative integer (timeout expressed in seconds)\n"
    "   - If [value] is positive, this sets a limit on the search time for the next\n"
    "     call to '(check)'.\n"
    "   - If [value] is zero, this clears the timeout. The next call to '(check)' is\n"
    "     not limited.\n" },

  { "show-timeout", HCOMMAND, "(show-timeout)",
    "Show the timeout value",
    NULL },

  { "help", HCOMMAND, "(help)",
    "Show a summary of the main commands",
    NULL },

  { "help", HCOMMAND, "(help [topic])",
    "Show help on a specific [topic]",
    "    [topic] can be\n"
    "       a YICES command    (help \"define-type\")\n"
    "       a type construct   (help \"scalar\")\n"
    "       a function         (help \"bv-mul\")\n"
    "       a parameter name   (help \"branching\")\n"
    "\n"
    "To see the list of all possible topics: type '(help topics)'.\n" },

  { "syntax", HMISC, NULL,
    "Syntax",
    "\n"
    "  <command> ::=\n"
    "         ( define-type <symbol> )\n"
    "       | ( define-type <symbol> <typedef> )\n"
    "       | ( define <symbol> :: <type> )\n"
    "       | ( define <symbol> :: <type> <expr> )\n"
    "       | ( assert <expr> )\n"
    "       | ( exit )\n"
    "       | ( check )\n"
    "       | ( push )\n"
    "       | ( pop )\n"
    "       | ( reset )\n"
    "       | ( show-model )\n"
    "       | ( eval <expr> )\n"
    "       | ( echo <string> )\n"
    "       | ( include <string> )\n"
    "       | ( set-param <symbol> <immediate-value> )\n"
    "       | ( show-param <symbol> )\n"
    "       | ( show-params )\n"
    "       | ( show-stats )\n"
    "       | ( reset-stats )\n"
    "       | ( set-timeout <number> )\n"
    "       | ( dump-context )\n"
    "       | ( help )\n"
    "       | ( help <symbol> )\n"
    "       | ( help <string> )\n"
    "\n"  
    "  <typedef> ::=\n"
    "         <type>\n"
    "      | ( scalar <symbol> ... <symbol> )\n"
    "\n"
    " <type> ::=\n"
    "         <symbol> \n"
    "       | ( tuple <type> ... <type> )\n"
    "       | ( -> <type> ... <type> <type> )\n"
    "       | ( bitvector <rational> )\n"
    "       | int\n"
    "       | bool\n"
    "       | real\n"
    "\n"
    " <expr> ::=\n"
    "         true\n"
    "       | false\n"
    "       | <symbol>\n"
    "       | <number>\n"
    "       | <binary bv>\n"
    "       | <hexa bv>\n"
    "       | ( forall ( <var_decl> ... <var_decl> ) <expr> )\n"
    "       | ( exists ( <var_decl> ... <var_decl> ) <expr> )\n"
    "       | ( lambda ( <var_decl> ... <var_decl> ) <expr> )\n"
    "       | ( let ( <binding> ... <binding> ) <expr> )\n"
    "       | ( update <expr> ( <expr> ... <expr> ) <expr> )\n"
    "       | ( <function> <expr> ... <expr> )\n"
    "\n"
    " <function> ::=\n"
    "         <function-keyword>\n"
    "       | <expr>\n"
    "\n"
    " <var_decl> ::= <symbol> :: <type>\n"
    "\n"
    " <binding> ::= ( <symbol> <expr> )\n"
    "\n"
    " <immediate-value> ::=  true | false | <number> | <symbol>\n"
    "\n"
    " <number> ::= <rational> | <float>\n"
    "\n" },

  // END MARKER
  { NULL, HMISC, NULL, NULL },
};


/*
 * For proper alignment in summary_help
 * - maximal length of the synopsis part in array help[0.. n-1]
 */
static uint32_t synopsis_width(const help_record_t **help, uint32_t n) {
  uint32_t len, max;
  uint32_t i;

  max = 0;
  for (i=0; i<n; i++) {
    len = strlen(help[i]->synopsis);
    if (len > max) {
      max = len;
    }
  }

  return max;
}


/*
 * Print n spaces
 */
static void spaces(FILE *f, uint32_t n) {
  while (n > 0) {
    fputc(' ', f);
    n --;
  }
}



/*
 * Display an array of help records:
 * - n = number of records (must be positive)
 * - help = the records themselves
 * - f = output stream
 *
 * If detailed is true: use the deailed format otherwise use
 * a compact format;
 *
 * Detailed format
 * ---------------
 * For each record: print
 *   <synopsis> 
 *   Short explanation
 *   Long explanation (if any)
 *   newline
 *
 * Compact format
 * --------------
 * one line per record:
 *   <synopsis>     Short explanation
 *
 * GAP = number of spaces between <synopsis> and Short explanation
 */
#define GAP 4

static void display_help(FILE *f, const help_record_t **help, uint32_t n, bool detailed) {
  uint32_t i, len, width;

  if (detailed) {
    for (i=0; i<n; i++) {
      fprintf(f, "\n%s\n\n%s\n", help[i]->synopsis, help[i]->short_expl);
      if (help[i]->long_expl != NULL) {
	fputs(help[i]->long_expl, f);
      }
    }
    fputc('\n', f);
  } else {
    // Compact format
    width = synopsis_width(help, n) + GAP;
    for (i=0; i<n; i++) {
      len = strlen(help[i]->synopsis);
      assert(len < width);
      fputs(help[i]->synopsis, f);
      spaces(f, width - len);
      fputs(help[i]->short_expl, f);
      fputc('\n', f);
    }
  }

}



/*
 * Vector to collect pointers to help records
 */
typedef struct help_vector_s {
  uint32_t size;
  uint32_t nelems;
  const help_record_t **data;
} help_vector_t;

#define DEF_HELP_VECTOR_SIZE 100
#define MAX_HELP_VECTOR_SIZE (UINT32_MAX/sizeof(help_record_t *))

static void init_hvector(help_vector_t *v) {
  uint32_t n;

  n = DEF_HELP_VECTOR_SIZE;
  assert(n <= MAX_HELP_VECTOR_SIZE);

  v->size = n;
  v->nelems = 0;
  v->data = (const help_record_t **) safe_malloc(n * sizeof(help_record_t *));
}


static void extend_hvector(help_vector_t *v) {
  uint32_t n;

  n = v->size << 1;
  if (n > MAX_HELP_VECTOR_SIZE) {
    out_of_memory();
  }

  v->size = n;
  v->data = (const help_record_t **) safe_realloc(v->data, n * sizeof(help_record_t *));
}

static void delete_hvector(help_vector_t *v) {
  safe_free(v->data);
  v->data = NULL;
}

static void hvector_push(help_vector_t *v, const help_record_t *r) {
  uint32_t i;

  i = v->nelems;
  if (i == v->size) {
    extend_hvector(v);
  }
  assert(i < v->size);
  v->data[i] = r;
  v->nelems = i+1;
}



/*
 * COLLECT HELP RECORDS INTO A VECTOR
 */

/*
 * Collect all help records that match the given topic:
 * - i.e., all those records r such that r->name == topic
 */
static void collect_topic(help_vector_t *v, const char *topic) {
  const help_record_t *r;

  for (r = help_data; r->name != NULL; r ++) {
    if (strcmp(topic, r->name) == 0) {
      hvector_push(v, r);
    }
  }
}


/*
 * Collect all help records of a given category
 */
static void collect_category(help_vector_t *v, htype_t cat) {
  const help_record_t *r;

  for (r = help_data; r->name != NULL; r ++) {
    if (r->category == cat) {
      hvector_push(v, r);
    }
  }
}



void show_help(FILE *f, const char *topic) {
  help_vector_t v;

  init_hvector(&v);

  if (topic == NULL) {
    collect_category(&v, HCOMMAND);
    fputs("\nCommand Summary:\n\n", f);
    display_help(f, v.data, v.nelems, false);
    fputs("\nFor a list of all help topics: type '(help topics)'.\n", f);
  } else {
    collect_topic(&v, topic);
    if (v.nelems == 0) {
      fputs("\nFound nothing relevant\n", f);
      fputc('\n', f);
    } else {
      display_help(f, v.data, v.nelems, true);
    }
  }

  delete_hvector(&v);
}
