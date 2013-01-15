/*
 * Help command for Yices
 */

#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#include "int_vectors.h"
#include "yices_help.h"



/*
 * Help descriptors
 * ----------------
 * - each command, type and term constructor, and parameter is described
 *   by a help record that includes:
 *   - category code
 *   - synopsis
 *   - summary description
 *   - detailed description
 *   - examples
 *  
 * All descriptors are stored in a global array 'help_data'
 *
 * * Some commands exist in two variants. Each variant is described by its
 * own record. The two variants must appear one after the other in the 
 * help array.
 *
 * Example for define-type:
 * - category: COMMAND
 * - synopsis: "(define-type [name] [typedef])"
 * - summary: Define a new type
 * - detail: multiple lines of text
 * - examples: also several lines of text
 *
 * The detailed description and examples may be NULL.
 *
 * Help index
 * ----------
 * - for each help topic, we use a record that describes how to 
 *   display the corresponding help message.
 * - the record includes:
 *   - key = topic name (string)
 *   - aux = another string (or NULL)
 *   - idx = an integer index
 *   - proc = a function pointer
 *
 * - proc has signature: 
 *     void proc(FILE *f, const char *key, const char *aux, int32_t idx)
 *
 * - when processing "help(f, topic):
 *   search for a record r with key equal to topic
 *   then call r->proc(f, topic, r->aux, r->idx)
 *
 * For most topics: aux is NULL, idx is the index of a descriptor in help_data,
 * and proc is a function that formats/displays help_data[idx].
 *
 * For commands that exist in two variants:
 * - aux = heading to display (like summary)
 * - idx = index in help_data
 * - proc: displays aux then help_data[idx] and help_data[idx + 1].
 *
 * Some topics scan the help_data array, collect relevant records (based on category)
 * then display a summary of all these records.
 * - aux = NULL
 * - idx = category
 * - proc: function to collect then display the list of relevant records
 *
 * Other versions of the proc function TBD.
 */

/*
 * HELP DESCRIPTORS
 */
// categories
typedef enum {
  HCOMMAND,     // Yices command
  HTYPE,        // Types and type constructors
  HGENERIC,     // General constructs (apply to all types)
  HBOOLEAN,     // Boolean operators and constants
  HARITHMETIC,  // Arithmetic operators and constants
  HBITVECTOR,   // Bitvector operators
  HPARAM,       // Parameters (in (set-param ...)
  HMISC,        // Everything else
} htype_t;

typedef struct help_record_s {
  htype_t category;
  const char *synopsis;
  const char *summary;
  const char *detail;
  const char *example;
} help_record_t;


/*
 * HELP INDEX
 */
typedef void (*help_fun_t)(FILE *f, const char *topic, const char *aux, int32_t idx);

typedef struct help_index_s {
  const char *key;
  const char *aux;
  int32_t idx;
  help_fun_t proc;
} help_index_t;


/*
 * DATA
 */
static const help_record_t help_data[] = {
  // define-type: index 0
  { HCOMMAND,
    "(define-type [name])",
    "Declare a new uninterpreted type", 
    "   [name] must be a fresh name\n",
    "(define-type T)\n" },

  { HCOMMAND, 
    "(define-type [name] [typedef])",
    "Define a new type",
    "   [name] must be a fresh name\n"
    "   [typedef] can be\n"
    "      a primitive type: 'bool', 'real', 'int', or '(bitvector k)'\n"
    "      a function type:  '(-> [type] ... [type])'\n"
    "      a tuple type:     '(tuple [type] ... [type])'\n"
    "      a scalar type:    '(scalar [name] .... [name])'\n",
    "(define-type pred (-> int bool))\n"
    "(define-type color (scalar red black white))\n" },

  // define: index 2
  { HCOMMAND, 
    "(define [name] :: [type])",
    "Declare a new uninterpreted constant",
    "   [name] must be fresh\n",
    "(define x :: int)\n"
    "(define f :: (-> T bool)\n" },
  

  { HCOMMAND, 
    "(define [name] :: [type] [expr])",
    "Define a new constant",
    "   [name] must be fresh\n"
    "   [expr] must be an expression of type [type] or a subtype of [type]\n",
    "(define b::bool (and (< x 10) (> x 0)))\n" },

  // assert: index 4
  { HCOMMAND,
    "(assert [expr])",
    "Add an assertion to the logical context",
    "   [expr] must be a Boolean expression\n",
    "(assert (or (= a (f 10)) (/= x (g (g a)))))\n" },

  // check: index 5
  { HCOMMAND, 
    "(check)",
    "Check whether the logical context is satisfiable",
    NULL,
    NULL  },

  // push: index 6
  { HCOMMAND, 
    "(push)", 
    "Start a new assertion scope",
    "All assertions added after '(push)' can be later retracted by '(pop)'\n"
    "\n"
    "Note: (push) and (pop) are not supported if yices is invoked with\n"
    "'--mode=one-shot' or '--mode=multi-checks'.\n" ,
    NULL },

  // pop: index 7
  { HCOMMAND,
    "(pop)",
    "Remove all assertions added since the matching (push)",
    "This does not remove term or type declarations, only the assertions\n"
    "\n"
    "Note: (push) and (pop) are not supported if yices is invoked with\n"
    "'--mode=one-shot' or '--mode=multi-checks'\n",
    NULL },

  // reset: index 8
  { HCOMMAND, 
    "(reset)", 
    "Reset the logical context (to the empty context)",
    "All assertions are removed, Type and term declarations are kept.\n",
    NULL },

  // show-model: index 9
  { HCOMMAND,
    "(show-model)",
    "Show the current model",
    "Displays the model if one is available, that is, after a call to (check)\n"
    "that returns 'sat' or 'unknown'.\n",
    NULL },

  // eval: index 10
  { HCOMMAND, 
    "(eval [expr])",
    "Evaluate an expression in the current model",
    "This may be used after a call to (check) that returns 'sat' or 'unknown'.\n",
    "(eval (+ x (* 2 y) -3))\n" },

  // include: index 11
  { HCOMMAND,
    "(include [filename])",
    "Read commands from a file",
    "   [filename] must be given as a string as in \"example.ys\"\n",
    NULL },

  // echo: index 12
  { HCOMMAND,
    "(echo [string])",
    "Output a message",
    NULL,
    NULL },

  // set-param: index 13
  { HCOMMAND, 
    "(set-param [name] [value])",
    "Set a parameter",
    "   [name] must be a parameter name\n"
    "   [value] must be an immediate value (i.e., a number, Boolean, or symbol)\n"
    "\n"
    "Parameters control the preprocessing, simplification, and search\n"
    "heuristics used by Yices. Type '(help params)' to see the list of\n"
    "all parameters.\n",
    "(set-param branching negative)\n"
    "(set-param flatten false)\n"
  },

  // show-param: index 14
  { HCOMMAND,
    "(show-param [name])",
    "Show the value of a parameter",
    "\n"
    "Type '(help params)' to see the list of all parameters.\n",
    "(show-param branching)\n"
    "(show-param random-seed)\n" },

  // show-params: index 15
  { HCOMMAND, 
    "(show-params)",
    "Show all parameters and their current value",
    NULL,
    NULL },

  // show-stats: index 16
  { HCOMMAND, 
    "(show-stats)",
    "Show statistics",
    "Display various counters and statistics about '(check)'\n",
    NULL},

  // reset-stats: index 17
  { HCOMMAND, 
    "(reset-stats)",
    "Reset the statistics counters",
    NULL,
    NULL },

  // set-timeout: index 18
  { HCOMMAND, 
    "(set-timeout [value])",
    "Give a timeout",
    "   [value] must be a non-negative integer (timeout expressed in seconds)\n"
    "   - if [value] is positive, this sets a limit on the search time for the next\n"
    "     call to '(check)'.\n"
    "   - if [value] is zero, this clears the timeout. The next call to '(check)' is\n"
    "     not limited.\n"
    "\n"
    "The timeout is reset after every call to '(check)'\n",
    NULL,
  },

  // show-timeout: index 19
  { HCOMMAND, 
    "(show-timeout)",
    "Show the timeout value",
    NULL,
    NULL },

  // help: index 20
  { HCOMMAND, 
    "(help)",
    "Show a summary of the main commands",
    NULL,
    NULL },

  { HCOMMAND, 
    "(help [topic])",
    "Show help on a specific topic",
    "    [topic] can be\n"
    "       a command          (help \"define-type\")\n"
    "       a type construct   (help \"scalar\")\n"
    "       a function         (help \"bv-mul\")\n"
    "       a parameter name   (help \"branching\")\n"
    "\n"
    "To see the list of all topics: type '(help index)'.\n",
    NULL },

  // exit: index 22
  { HCOMMAND,
    "(exit)",
    "Quit Yices",
    NULL,
    NULL },

  // bool: index 23
  { HTYPE, "bool", "Boolean type", NULL, NULL },

  // int: index 24
  { HTYPE, "int", "Integer type", NULL, NULL },

  // real: index 25
  { HTYPE, "real", "Real type", NULL, NULL },

  // bitvector: index 26
  { HTYPE, 
    "(bitvector [k])",
    "Bitvectors of [k] bits",
    "   [k] must be positive\n",
    "(bitvector 32)\n" },

  // scalar: index 27
  { HTYPE,
    "(define-type [name] (scalar [elem_1] ... [elem_k]))",
    "Enumeration type",
    "   [name] must be fresh\n"
    "   [elem_1] ... [elem_k] must be distinct fresh names\n"
    "\n"
    "This declaration introduces [name] as a new type of k elements.\n"
    "This also introduces k constants [elem_1] ... [elem_k] of type [name]\n",
    "(define-type singleton (scalar A))\n"
    "(define-type day (scalar Mon Tue Wed Thu Fri Sat Sun))\n" },

  // tuple: index 28
  { HTYPE,
    "(tuple [type_1] ... [type_n])",
    "Tuple type",
    NULL,
    "(define p::(tuple int int) (mk-tuple 0 1))\n"
    "(define-type pair (tuple real real))\n" },

  // ->: index 29
  { HTYPE,
    "(-> [type_1] ... [type_n] [tau])",
    "Function type",
    "This is the type of functions of domain [type_1] x ... x [type_n] and range [tau]\n",
    "(define-type relation (-> int int bool))\n"
    "(define f :: (-> int int))\n" },

  // ite: index 30
  { HGENERIC,
    "(ite [condition] [expr1] [expr2])",
    "If-then-else",
    "   [condition] must be a Boolean expression\n"
    "   [expr1] and [expr2] must have compatible types\n"
    "\n"
    "The expression '(ite c t1 t2)' means 'if c then t1 else t2'\n",
    "(define min::real (ite (< x y) x y))\n" },

  // if: index 31
  { HGENERIC,
    "(if  [condition] [expr1] [expr2])",
    "If-then-else",
    "'if' is a synonym for 'ite'. Try '(help ite)' for details\n",
    NULL },

  // =: index 32
  { HGENERIC,
    "(=  [expr1] [expr2])",
    "Equality",
    "   [expr1] and [expr2] must have compatible types\n",
    NULL },

  // /=: index 33
  { HGENERIC,
    "(/= [expr1] [expr2])",
    "Disequality",
    "   [expr1] and [expr2] must have compatible types\n",
    NULL },

  // distinct: index 34
  { HGENERIC,
    "(distinct [expr1] [expr2] ... [expr_k])",
    "Distinct",
    "   [expr1] ... [expr_k] must have compatible types\n"
    "\n"
    "   (distinct t1 ... tk) is true if t1 ... tk are pairwise distinct\n",
    NULL },

  // mk-tuple: index 35
  { HGENERIC,
    "(mk-tuple [expr1] ... [expr_k])",
    "Tuple constructor",
    NULL,
    NULL },

  // select: index 36
  { HGENERIC,
    "(select [tuple] [index])",
    "Tuple projection",
    "   [tuple] must be an expression of tuple type\n"
    "   [index] must be an integer between 1 and the tuple's arity\n",
    "(select (mk-tuple x y) 2)   is equal to y\n"
    "(select (mk-tuple a) 1)     is equal to a\n" },

  // tuple-update: index 37
  { HGENERIC,
    "(tuple-update [tuple] [index] [expr])",
    "Tuple update",
    "   [tuple] must be an expression of tuple type\n"
    "   [index] must be an integer between 1 and the tuple's arity\n"
    "\n"
    "   (tuple-update t1 i e) is the tuple equal to t1 but with the i-th\n"
    "   component replaced by e\n",
    "(tuple-update (mk-tuple x y) 2 1)   is equal to (mk-tuple x 1)\n" },

  // update: index 38
  { HGENERIC,
    "(update [function] ([arg_1] ... [arg_n]) [expr])",
    "Function/array update",
    "   (update f (t1 ... t_n) v) is a function of same type as f.\n"
    "   It maps (t_1 ... t_n) to v and agrees with f on all other points.\n",
    NULL },

  // true: index 39
  { HBOOLEAN, "true", "Boolean constant", NULL, NULL },

  // false: index 40
  { HBOOLEAN, "false", "Boolean constant", NULL, NULL },

  // or: index 41
  { HBOOLEAN,
    "(or  [expr_1] ... [expr_n])",
    "Disjunction",
    "   [expr_1] ... [expr_n] must be Boolean expressions\n",
    NULL },

  // and: index 42
  { HBOOLEAN,
    "(and [expr_1] ... [expr_n])",
    "Conjunction",
    "   [expr_1] ... [expr_n] must be Boolean expressions\n",
    NULL },
    
  // not: index 43
  { HBOOLEAN,
    "(not [expr])",
    "Boolean negation",
    "   [expr] must be a Boolean expression\n",
    NULL },

  // xor: index 44
  { HBOOLEAN,
    "(xor [expr1] ... [expr_n])",
    "Exclusive or",
    "   [expr_1] ... [expr_n] must be Boolean expressions\n",
    NULL },

  // <=>: index 45
  { HBOOLEAN,
    "(<=> [expr1] [expr2])",
    "Boolean equivalence",
    "   [expr1] and [expr2] must be Boolean expression\n"
    "\n"
    "   (<=> t1 t2) is the same as (= t1 t2) if t1 and t2 are Boolean\n",
    NULL },

  // =>: index 46
  { HBOOLEAN,
    "(=>  [expr1] [expr2])",
    "Implication",
    "   [expr1] and [expr2] must be Boolean expression\n"
    "\n"
    "'(=> t1 t2)' means 't1 implies t2'\n",
    NULL },

  // +: index 47
  { HARITHMETIC,
    "(+ [expr_1] ... [expr_n])", 
    "Addition",
    "   [expr_1] ... [expr_n] must be arithmetic expressions\n",
    NULL },

  // -: index 48
  { HARITHMETIC,
    "(- [expr_1] ... [expr_n])",
    "Subtraction",
    "   [expr_1] ... [expr_n] must be arithmetic expressions\n"
    "\n"
    "   (- t1 t2 t3 ... t_n) is interpreted as t1 - t2 - t3 ... - t_n\n",
    NULL },

  // -: index 49
  { HARITHMETIC,
    "(- [expr])",
    "Negation",
    "   [expr] must be an arithmetic expressions\n",
    NULL },

  // *: index 50
  { HARITHMETIC,
    "(* [expr_1] ... [expr_n])",
    "Product",
    "   [expr_1] ... [expr_n] must be arithmetic expressions\n",
    NULL },

  // /: index 51
  { HARITHMETIC,
    "(/ [expr] [divider])",
    "Division",
    "   [expr] must be an arithmetic expression\n"
    "   [divider] must be a non-zero arithmetic constant\n",
    "(/ x 2)\n" },

  // ^: index 52
  { HARITHMETIC,
    "(^ [expr] [exponent])",
    "Exponentiation",
    "   [expr] must be an arithmetic expression\n"
    "   [exponent] must be a non-negative integer constant\n",
    "(^ (+ x y) 2)\n" },

  // <: index 53
  { HARITHMETIC,
    "(<  [expr1] [expr2])",
    "Less than",
    "   [expr1] and [expr2] must be arithmetic expressions\n",
    NULL },

  // >: index 54
  { HARITHMETIC,
    "(>  [expr1] [expr2])",
    "Greater than",
    "   [expr1] and [expr2] must be arithmetic expressions\n",
    NULL },

  // <=: index 55
  { HARITHMETIC,
    "(<= [expr1] [expr2])",
    "Less than or equal",
    "   [expr1] and [expr2] must be arithmetic expressions\n",
    NULL },

  // >=: index 56
  { HARITHMETIC,
    "(>= [expr1] [expr2])",
    "Greater than or equal",
    "   [expr1] and [expr2] must be arithmetic expressions\n",
    NULL },

  // mk-bv: index 57
  { HBITVECTOR,
    "(mk-bv [size] [value])",
    "Convert an integer into a bitvector constant",
    "   [size] must be a positive integer (number of bits)\n"
    "   [value] must be a non-negative integer\n"
    "\n"
    "The bitvector constant (mk-bv n x) is the binary representation of (x mod 2^n)\n",
    "(mk-bv 6 0)     is equal to 0b000000\n"
    "(mk-bv 6 127)   is equal to 0b111111\n"},

  // bv-add: index 58
  { HBITVECTOR,
    "(bv-add [expr1] [expr2])",
    "Bitvector addition",
    "   [expr1] and [expr2] must be two bitvector expressions of same size\n"
    "   the result has the same number of bits as [expr1] and [expr2]\n",
    NULL },

  // bv-sub: index 59
  { HBITVECTOR,
    "(bv-sub [expr1] [expr2])",
    "Bitvector subtraction",
    "   [expr1] and [expr2] must be two bitvector expressions of same size\n"
    "   the result has the same number of bits as [expr1] and [expr2]\n",
    NULL },

  // bv-mul: index 60
  { HBITVECTOR,
    "(bv-mul [expr1] [expr2])",
    "Bitvector multiplication",
    "   [expr1] and [expr2] must be two bitvector expressions of same size\n"
    "   the result has the same number of bits as [expr1] and [expr2]\n",
    NULL },

  // bv-neg: index 61
  { HBITVECTOR,
    "(bv-neg [expr])",
    "Bitvector opposite",
    "   (bv-neg [expr]) is the opposite of {expr] in 2s complement representation\n",
    NULL },

  // bv-pow: index 62
  { HBITVECTOR,
    "(bv-pow [expr] [exponent])",
    "Bitvector exponentiation",
    "   [expr] must be a bitvector expression\n"
    "   [exponent] must be a non-negative integer constant\n"
    "   the result has the same number of bits as [expr]\n",
    "(bv-pow (bv-add x y) 2)\n" },

  // bv-not: index 63
  { HBITVECTOR,
    "(bv-not [expr])",
    "Bitwise complement",
    NULL,
    NULL },

  // bv-and: index 64
  { HBITVECTOR,
    "(bv-and [expr1] [expr2])",
    "Bitwise and",
    "   [expr1] and [expr2] must be bitvectors of the same size\n",
    NULL },

  // bv-or: index 65
  { HBITVECTOR,
    "(bv-or [expr1] [expr2])",
    "Bitwise or",
    "   [expr1] and [expr2] must be bitvectors of the same size\n",
    NULL },

  // bv-xor: index 66
  { HBITVECTOR,
    "(bv-xor [expr1] [expr2])",
    "Bitwise exclusive or",
    "   [expr1] and [expr2] must be bitvectors of the same size\n",
    NULL },

  // bv-nand: index 67
  { HBITVECTOR,
    "(bv-nand [expr1] [expr2])",
    "Bitwise nand",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "   (bv-nand x y) is the same as (bv-not (bv-and x y))\n",
    NULL },
  
  // bv-nor: index 68
  { HBITVECTOR,
    "(bv-nor [expr1] [expr2])",
    "Bitwise nor",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "   (bv-nor x y) is the same as (bv-not (bv-or x y))\n",
    NULL },

  // bv-xnor: index 69
  { HBITVECTOR,
    "(bv-xnor [expr1] [expr2])",
    "Bitwise not xor",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "   (bv-xnor x y) is the same as (bv-not (bv-xor x y))\n",
    NULL },

  // bv-shift-left0: index 70
  { HBITVECTOR,
    "(bv-shift-left0 [expr] [shift-amount])",
    "Shift left by a constant, padding with 0",
    "    [shift-amount] must be an integer between 0 and the size of [expr]\n",
    "(bv-shift-left0 0b011000 2)  is equal to 0b100000\n"
    "(bv-shift-left0 0b011000 7)  is incorrect\n" },

  // bv-shift-left1: index 71
  { HBITVECTOR,
    "(bv-shift-left1 [expr] [shift-amount])",
    "Shift left by a constant, padding with 1",
    "    [shift-amount] must be an integer between 0 and the size of [expr]\n",
    "(bv-shift-left1 0b011000 2)  is equal to 0b100011\n"
    "(bv-shift-left1 0b011000 7)  is incorrect\n" },

  // bv-shift-right0: index 72
  { HBITVECTOR,
    "(bv-shift-right0 [expr] [shift-amount])",
    "Shift right by a constant, padding with 0",
    "    [shift-amount] must be an integer between 0 and the size of [expr]\n",
    "(bv-shift-right0 0b011000 2)  is equal to 0b000110\n"
    "(bv-shift-right0 0b011000 7)  is incorrect\n" },

  // bv-shift-right1: index 73
  { HBITVECTOR,
    "(bv-shift-right1 [expr] [shift-amount])",
    "Shift right by a constant, padding with 1",
    "    [shift-amount] must be an integer between 0 and the size of [expr]\n",
    "(bv-shift-right1 0b011000 2)  is equal to 0b110110\n"
    "(bv-shift-right1 0b011000 7)  is incorrect\n" },

  // bv-ashift-right: index 74
  { HBITVECTOR,
    "(bv-ashift-right [expr] [shift-amount])",
    "Arithmetic shift by a constant",
    "    [shift-amount] must be an integer between 0 and the size of [expr]\n"
    "\n"
    "[expr] is shifted by the given amount padding with [expr]'s sign bit\n",
    "(bv-ashift-right 0b011000 2)   is equal to 0b000110\n"
    "(bv-ashift-right 0b111000 2)   is equal to 0b111110\n" },

  // bv-rotate-left: index 75
  { HBITVECTOR,
    "(bv-rotate-left [expr] [shift-amount])",
    "Rotate to the left by a constant amount",
    "    [shift-amount] must be an integer between 0 and the size of [expr]\n",
    "(bv-rotate-left 0b011000 2)  is equal to 0b100001\n" },

  // bv-rotate-right: index 76
  { HBITVECTOR,
    "(bv-rotate-rightt [expr] [shift-amount])",
    "Rotate to the right by a constant amount",
    "    [shift-amount] must be an integer between 0 and the size of [expr]\n",
    "(bv-rotate-right 0b011001 2)  is equal to 0b010110\n" },

  // bv-shl: index 77
  { HBITVECTOR,
    "(bv-shl [expr1] [expr2])",
    "Left shift",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-shl x y) is x shifted to the left by k bits and padded with 0\n"
    "             where k is the value of y, interpreted as an unsigned integer\n"
    "If k is larger than the size of x, then the result is the zero bitvector '0b0...0\n",
    "(bv-shl 0b011001 0b000010)  is equal to 0b100100\n"
    "(bv-shl 0b011001 0b110000)  is equal to 0b000000\n" },

  // bv-lshr: index 78
  { HBITVECTOR,
    "(bv-lshr [expr1] [expr2])",
    "Logical right shift",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-lshr x y) is x shifted to the right by k bits and padded with 0\n"
    "              where k is the value of y, interpreted as an unsigned integer\n"
    "If k is larger than the size of x, then the result is the zero bitvector '0b0...0\n",
    "(bv-lshr 0b011001 0b000010)  is equal to 0b000110\n"
    "(bv-lshr 0b011001 0b110000)  is equal to 0b000000\n" },

  // bv-ashr: index 79
  { HBITVECTOR,
    "(bv-ashr [expr1] [expr2])",
    "Arithmetic right shift",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-ashr x y) is x shifted to the right by k bits and padded with x's sign bit\n"
    "              where k is the value of y, interpreted as an unsigned integer\n"
    "If k is larger than the size of x, then the result is either the zero bitvector\n"
    "'0b0...0, if x is non-negative or the vector 0b1...1 if x is negative\n",
    "(bv-ashr 0b011001 0b000010)  is equal to 0b000110\n"
    "(bv-lshr 0b111001 0b110000)  is equal to 0b111110\n" },

  // bv-extract: index 80
  { HBITVECTOR,
    "(bv-extract [high] [low] [expr])",
    "Subvector extraction",
    "   [expr] must be a bitvector expression\n"
    "   [high] and [low] must be integer constants\n"
    "\n"
    "(bv-extract i j x) extracts bits j, j+1, ..., i of x\n"
    "If x has n bits, then i and j must satisfy 0 <= j <= i <= n-1\n",
    "(bv-extract 0 3 0b011010)  is equal to 0b1010\n"
    "(bv-extract 1 1 0b011010)  is equal to 0b1\n" },

  /// bv-concat: index 81
  { HBITVECTOR,
    "(bv-concat [expr1] [expr2])",
    "Bitvector concatenation",
    NULL,
    "(bv-concat 0b100 0b11101  is equal to 0b10011101\n" },

  // bv-repeat: index 82
  { HBITVECTOR,
    "(bv-repeat [expr] [constant])",
    "Repeated concatenation",
    "   [expr] must be a bitvector expression\n"
    "   [constant] must be a positive integer\n"
    "\n"
    "(bv-repeat x n) is n copies of x concatenated together\n",
    "(bv-repeat 0b011010 3)   is equal to 0b011010011010011010\n" },

  // bv-sign-extend: index 83
  { HBITVECTOR,
    "(bv-sign-extend [expr] [constant])",
    "Sign extension",
    "   [expr] must be a bitvector expression\n"
    "   [constant] must be a non-negative integer\n"
    "\n"
    "(bv-sign-extend x n) adds n copies of x's sign bit to the left of x\n",
    "(bv-sign-extend 0b011010 3) is equal to 0b000011010\n"
    "(bv-sign-extend 0b111010 3) is equal to 0b111111010\n"
    "(bv-sign-extend 0b111010 0) is equal to 0b111010\n" },

  // bv-zero-extend: index 84
  { HBITVECTOR,
    "(bv-zero-extend [expr] [constant])",
    "Zero extension",
    "   [expr] must be a bitvector expression\n"
    "   [constant] must be a non-negative integer\n"
    "\n"
    "(bv-zero-extend x n) adds n zero bits to the left of x\n",
    "(bv-zero-extend 0b011010 3) is equal to 0b000011010\n"
    "(bv-zero-extend 0b111010 3) is equal to 0b000011010\n"
    "(bv-zero-extend 0b111010 0) is equal to 0b111010\n" },
  
  // bv-div: index 85
  { HBITVECTOR,
    "(bv-div [expr1] [expr2])",
    "Quotient in unsigned bitvector division",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-div x y) is the quotient in the unsigned division of x by y\n"
    "\n"
    "If y is 0b0...0 then the result is 0b1....1 (i.e., the largest unsigned\n"
    "integer representable using n bits\n",
    "(bv-div 0b10001 0b00101)  is equal to 0b00011  (i.e., 17 div 5 = 3)\n" },

  // bv-rem: index 86
  { HBITVECTOR,
    "(bv-rem [expr1] [expr2])",
    "Remainder in unsigned bitvector division",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-rem x y) is the quotient in the unsigned division of x by y\n"
    "\n"
    "If y is 0b0...0 then the result is x\n"
    "(bv-rem 0b10001 0b00101)  is equal to 0b00010  (i.e., 17 mod 5 = 2)\n" },

  // bv-sdiv: index 87
  { HBITVECTOR,
    "(bv-sdiv [expr1] [expr2])",
    "Quotient in signed bitvector division (rounding to 0)",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-sdiv x y) is the quotient of the signed division of x by y\n"
    "x and y are interpreted as integers in 2s complement representation\n"
    "\n"
    "If y is 0b0...0 then the result is 0b0... 01 (i.e., +1) if x's sign bit is 1\n"
    "or 0b1...1 (i.e., -1) if x's sign bit is 0.\n",
    NULL },

  // bv-srem: index 88
  { HBITVECTOR,
    "(bv-srem [expr1] [expr2])",
    "Remainder in signed bitvector division (rounding to 0)",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-srem x y) is the quotient of the signed division of x by y\n"
    "x and y are interpreted as integers in 2s complement representation\n"
    "\n"
    "If y is 0b0...0 then the result is x\n",
    NULL },
    
  // bv-smod: index 89
  { HBITVECTOR,
    "(bv-smod [expr1] [expr2])",
    "Remainder in signed bitvector division (rounding to -infinity)",
    "   [expr1] and [expr2] must be bitvectors of the same size\n"
    "\n"
    "(bv-srem x y) is the quotient of the signed division of x by y\n"
    "x and y are interpreted as integers in 2s complement representation\n"
    "\n"
    "If y is 0b0...0 then the result is x\n",
    NULL },
 
  // bv-redand: index 90
  { HBITVECTOR,
    "(bv-redand [expr])",
    "And reduction",
    "   [expr] must be a bitvector expression\n"
    "   The result is a bitvector of one bit\n"
    "\n"
    "(bv-redand x)  is 0b1 if all bits of x are 1\n"
    "               or 0b0 otherwise\n",
    NULL },

  // bv-redor: index 91
  { HBITVECTOR,
    "(bv-redor [expr])",
    "Or reduction",
    "   [expr] must be a bitvector expression\n"
    "   The result is a bitvector of one bit\n"
    "\n"
    "(bv-redor x)  is 0b0 if all bits of x are 0\n"
    "              or 0b1 otherwise\n",
    NULL },

  // bv-comp: index 92
  { HBITVECTOR,
    "(bv-comp [expr1] [expr2])",
    "Bitvector comparison",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "   The result is a bitvector of one bit\n"
    "\n"
    "(bv-comp x y) is equal to 0b1 if x and y are equal\n"
    "              or to 0b0 otherwise\n",
    NULL },

  // bv-ge: index 93
  { HBITVECTOR,
    "(bv-ge [expr1] [expr2])",
    "Unsigned bitvector comparison: greater than or equal",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-ge x y) is true if x >= y when x and y are interpreted as unsigned integers\n",
    NULL },

  // bv-gt: index 94
  { HBITVECTOR,
    "(bv-gt [expr1] [expr2])",
    "Unsigned bitvector comparison: greater than",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-gt x y) is true if x > y when x and y are interpreted as unsigned integers\n",
    NULL },

  // bv-le: index 95
  { HBITVECTOR,
    "(bv-le [expr1] [expr2])",
    "Unsigned bitvector comparison: less than or equal",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-le x y) is true if x <= y when x and y are interpreted as unsigned integers\n",
    NULL },

  // bv-lt: index 96
  { HBITVECTOR,
    "(bv-lt [expr1] [expr2])",
    "Unsigned bitvector comparison: less than or equal",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-lt x y) is true if x < y when x and y are interpreted as unsigned integers\n",
    NULL },

  // bv-sge: index 97
  { HBITVECTOR,
    "(bv-sge [expr1] [expr2])",
    "Signed bitvector comparison: greater than or equal",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-sge x y) is true if x >= y when x and y are interpreted as signed integers\n"
    "in 2s-complement representation\n",
    NULL },

  // bv-sgt: index 98
  { HBITVECTOR,
    "(bv-sgt [expr1] [expr2])",
    "Signed bitvector comparison: greater than",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-sgt x y) is true if x > y when x and y are interpreted as signed integers\n"
    "in 2s-complement representation\n",
    NULL },

  // bv-sle: index 99
  { HBITVECTOR,
    "(bv-sle [expr1] [expr2])",
    "Signed bitvector comparison: less than or equal",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-sle x y) is true if x <= y when x and y are interpreted as signed integers\n"
    "in 2s-complement representation\n",
    NULL },

  // bv-slt: index 100
  { HBITVECTOR,
    "(bv-slt [expr1] [expr2])",
    "Signed bitvector comparison: less than or equal",
    "   [expr1] and [expr2] must be a bitvectors of the same size\n"
    "\n"
    "(bv-slt x y) is true if x < y when x and y are interpreted as signed integers\n"
    "in 2s-complement representation\n",
    NULL },

  // END MARKER: index 101
  { HMISC, NULL, NULL, NULL, NULL },
};

#define END_HELP_DATA 101



/*`
 * Help messages for special topics
 */
#define syntax_summary \
  "\n" \
  "Syntax Summary\n" \
  "\n" \
  "  <command> ::=\n" \
  "         ( define-type <symbol> )\n" \
  "       | ( define-type <symbol> <typedef> )\n" \
  "       | ( define <symbol> :: <type> )\n" \
  "       | ( define <symbol> :: <type> <expr> )\n" \
  "       | ( assert <expr> )\n" \
  "       | ( exit )\n" \
  "       | ( check )\n" \
  "       | ( push )\n" \
  "       | ( pop )\n" \
  "       | ( reset )\n" \
  "       | ( show-model )\n" \
  "       | ( eval <expr> )\n" \
  "       | ( echo <string> )\n" \
  "       | ( include <string> )\n" \
  "       | ( set-param <symbol> <immediate-value> )\n" \
  "       | ( show-param <symbol> )\n" \
  "       | ( show-params )\n" \
  "       | ( show-stats )\n" \
  "       | ( reset-stats )\n" \
  "       | ( set-timeout <number> )\n" \
  "       | ( dump-context )\n" \
  "       | ( help )\n" \
  "       | ( help <symbol> )\n" \
  "       | ( help <string> )\n" \
  "\n"   \
  "  <typedef> ::=\n" \
  "         <type>\n" \
  "       | ( scalar <symbol> ... <symbol> )\n" \
  "\n" \
  "  <type> ::=\n" \
  "         <symbol> \n" \
  "       | ( tuple <type> ... <type> )\n" \
  "       | ( -> <type> ... <type> <type> )\n" \
  "       | ( bitvector <rational> )\n" \
  "       | int\n" \
  "       | bool\n" \
  "       | real\n" \
  "\n" \
  "  <expr> ::=\n" \
  "         true\n" \
  "       | false\n" \
  "       | <symbol>\n" \
  "       | <number>\n" \
  "       | <binary bv>\n" \
  "       | <hexa bv>\n" \
  "       | ( forall ( <var_decl> ... <var_decl> ) <expr> )\n" \
  "       | ( exists ( <var_decl> ... <var_decl> ) <expr> )\n" \
  "       | ( lambda ( <var_decl> ... <var_decl> ) <expr> )\n" \
  "       | ( let ( <binding> ... <binding> ) <expr> )\n" \
  "       | ( update <expr> ( <expr> ... <expr> ) <expr> )\n" \
  "       | ( <function> <expr> ... <expr> )\n" \
  "\n" \
  "  <function> ::=\n" \
  "         <function-keyword>\n" \
  "       | <expr>\n" \
  "\n" \
  "  <var_decl> ::= <symbol> :: <type>\n" \
  "\n" \
  "  <binding> ::= ( <symbol> <expr> )\n" \
  "\n" \
  "  <immediate-value> ::=  true | false | <number> | <symbol>\n" \
  "\n" \
  "  <number> ::= <rational> | <float>\n"




/*
 * DISPLAY PROCEDURES
 */

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
 * Print string s with a left-margin of n spaces
 */
static void print_with_margin(FILE *f, const char *s, uint32_t n) {
  bool new_line;

  new_line = true;
  while (*s != '\0') {
    if (new_line) spaces(f, n);
    fputc(*s, f);
    new_line = (*s == '\n');
    s ++;
  }
}


/*
 * Check whether s is a single or multiple lines
 */
static bool multiple_lines(const char *s) {
  uint32_t new_lines;

  new_lines = 0;
  while (*s != '\0') {
    if (*s == '\n') {
      new_lines ++;
      if (new_lines > 1) break;
    }
    s ++;
  }

  return new_lines >= 2;
}


/*
 * Maximal length of the synopsis for a list of records
 * - a = array of indices in array help_data
 * - n = length of a
 */
static uint32_t synopsis_width(int32_t *a, uint32_t n) {
  uint32_t i, len, max;
  int32_t j;

  max = 0;
  for (i=0; i<n; i++) {
    j = a[i];
    assert(0 <= j && j < END_HELP_DATA);
    len = strlen(help_data[j].synopsis);
    if (len > max) {
      max = len;
    }
  }

  return max;
}



/*
 * Display a list of help records in a compact format.
 * - for each record, we print one line:
 *   <synopsis>    summary
 * - the list of records to display is stored in vector v
 * - each element of v is an index in array help_data
 */

// MARGIN = number of spaced before the first column
// GAP = number of spaces between the two columns
#define MARGIN 2
#define GAP 4

static void display_summary(FILE *f, ivector_t *v) {
  uint32_t i, n, len, width;
  int32_t j;

  n = v->size;
  width = synopsis_width(v->data, n) + GAP;
  for (i=0; i<n; i++) {
    j = v->data[i];
    assert(0 <= j && j< END_HELP_DATA);
    len = strlen(help_data[j].synopsis);
    assert(len + GAP <= width);
    spaces(f, MARGIN);
    fputs(help_data[j].synopsis, f);
    spaces(f, width - len);
    fputs(help_data[j].summary, f);
    fputc('\n', f);
  }
}


/*
 * Collect all help records with category c
 * - store their index in vector v
 */
static void collect_records(ivector_t *v, htype_t c) {
  uint32_t i;

  for (i=0; i<END_HELP_DATA; i++) {
    if (help_data[i].category == c) {
      ivector_push(v, i);
    }
  }
}


/*
 * HELP PROCEDURES
 */

// basic help: format and display help_data[idx]
static void help_basic(FILE *f, const char *topic, const char *aux, int32_t idx) {
  const help_record_t *r;

  assert(0 <= idx && idx < END_HELP_DATA);
  r = help_data + idx;
  fprintf(f, "\n%s: %s\n", topic, r->summary);
  fprintf(f, "\nSynopsis: %s\n", r->synopsis);
  if (r->detail != NULL) {
    fputc('\n', f);
    fputs(r->detail, f);
    fputc('\n', f);
  }
  if (r->example != NULL) {
    fputs("Example", f);
    if (multiple_lines(r->example)) {
      fputc('s', f); // more than one example.
    }
    fputs(":\n\n", f);
    print_with_margin(f, r->example, 3);
    fputc('\n', f);
  }
}

// help for commands with two variants: display help_data[idx] and help_data[idx + 1]
// aux is used as common heading in this case
static void help_variant(FILE *f, const char *topic, const char *aux, int32_t idx) {
  const help_record_t *r1;
  const help_record_t *r2;

  assert(0 <= idx && idx + 1 < END_HELP_DATA);

  r1 = help_data + idx;
  r2 = r1 + 1;

  fprintf(f, "\n%s: %s\n\n", topic, aux);

  fprintf(f, "First form: %s\n", r1->synopsis);
  fputs(r1->summary, f);
  fputc('\n', f);
  if (r1->detail != NULL) {
    fputc('\n', f);
    fputs(r1->detail, f);
    fputc('\n', f);
  }

  fprintf(f, "\nSecond from: %s\n", r2->synopsis);
  fputs(r2->summary, f);
  fputc('\n', f);
  if (r2->detail != NULL) {
    fputc('\n', f);
    fputs(r2->detail, f);
    fputc('\n', f);
  }

  if (r1->example != NULL || r2->example != NULL) {
    fputs("Example", f);
    if ((r1->example != NULL && r2->example != NULL) 
	|| (r1->example != NULL && multiple_lines(r1->example))
	|| (r2->example != NULL && multiple_lines(r2->example))) {
      fputc('s', f);
    }
    fputs(":\n\n", f);
    if (r1->example != NULL) {
      print_with_margin(f, r1->example, 3);
    }
    if (r2->example != NULL) {
      print_with_margin(f, r2->example, 3);
    }
    fputc('\n', f);
  }
}

// collect all records with category = idx
// display the result as a compact list
static void help_for_category(FILE *f, const char *topic, const char *aux, int32_t idx) {
  ivector_t v;

  init_ivector(&v, 50);
  collect_records(&v, idx);

  if (aux != NULL) {
    fputc('\n', f);
    fputs(aux, f);
    fputc('\n', f); 
  }
  fputc('\n', f); 
  display_summary(f, &v);
  fputc('\n', f);

  delete_ivector(&v);
}

// for special topics such as 'syntax': just print aux
static void help_special(FILE *f, const char *topic, const char *aux, int32_t ix) {
  fputs(aux, f);
  fputc('\n', f);
}




/*
 * INDEX TABLE
 */
static const help_index_t help_index[] = {
  { "*", NULL, 50, help_basic },
  { "+", NULL, 47, help_basic },
  { "-", "Subtraction", 48, help_variant },
  { "->", NULL, 29, help_basic },
  { "/", NULL, 51, help_basic },
  { "/=", NULL, 33, help_basic },
  { "<", NULL, 53, help_basic },
  { "<=", NULL, 55, help_basic },
  { "<=>", NULL, 45, help_basic },
  { "=", NULL, 32, help_basic },
  { "=>", NULL, 46, help_basic },
  { ">", NULL, 54, help_basic },
  { ">=", NULL, 56, help_basic },
  { "and", NULL, 42, help_basic },
  { "arithmetic", "Arithmetic Operators", HARITHMETIC, help_for_category },
  { "assert", NULL, 4, help_basic },
  { "bitvector", NULL, 26, help_basic },
  { "bitvectors", "Bitvector Operators", HBITVECTOR, help_for_category },
  { "bool", NULL, 23, help_basic },
  { "booleans", "Boolean Operators", HBOOLEAN, help_for_category },
  { "bv-add", NULL, 58, help_basic },  
  { "bv-and", NULL, 64, help_basic },
  { "bv-ashift-right", NULL, 74, help_basic },
  { "bv-ashr", NULL, 79, help_basic },
  { "bv-comp", NULL, 92, help_basic },
  { "bv-concat", NULL, 81, help_basic },
  { "bv-div", NULL, 85, help_basic },
  { "bv-extract", NULL, 80, help_basic },
  { "bv-ge", NULL, 93, help_basic },
  { "bv-gt", NULL, 94, help_basic },
  { "bv-le", NULL, 95, help_basic },
  { "bv-lt", NULL, 96, help_basic },
  { "bv-lshr", NULL, 78, help_basic },
  { "bv-mul", NULL, 60, help_basic },  
  { "bv-nand", NULL, 67, help_basic },
  { "bv-neg", NULL, 61, help_basic },
  { "bv-nor", NULL, 68, help_basic },
  { "bv-not", NULL, 63, help_basic },
  { "bv-or", NULL, 65, help_basic },
  { "bv-pow", NULL, 62, help_basic },
  { "bv-redand", NULL, 90, help_basic },
  { "bv-redor", NULL, 91, help_basic },
  { "bv-rem", NULL, 86, help_basic },
  { "bv-repeat", NULL, 82, help_basic },
  { "bv-rotate-left", NULL, 75, help_basic },
  { "bv-rotate-right", NULL, 76, help_basic },
  { "bv-sdiv", NULL, 87, help_basic },
  { "bv-sge", NULL, 97, help_basic },
  { "bv-sgt", NULL, 98, help_basic },
  { "bv-shift-left0", NULL, 70, help_basic },
  { "bv-shift-left1", NULL, 71, help_basic },
  { "bv-shift-right0", NULL, 72, help_basic },
  { "bv-shift-right1", NULL, 73, help_basic },
  { "bv-shl", NULL, 77, help_basic },
  { "bv-sign-extend", NULL, 83, help_basic },
  { "bv-sle", NULL, 99, help_basic },
  { "bv-slt", NULL, 100, help_basic },
  { "bv-smod", NULL, 89, help_basic },
  { "bv-srem", NULL, 88, help_basic },
  { "bv-sub", NULL, 59, help_basic }, 
  { "bv-xnor", NULL, 69, help_basic },
  { "bv-xor", NULL, 66, help_basic },
  { "bv-zero-extend", NULL, 84, help_basic },
  { "check", NULL, 5, help_basic },
  { "commands", "Command Summary", HCOMMAND, help_for_category },
  { "define", "Declare or define a term", 2, help_variant },
  { "define-type", "Declare or define a type", 0, help_variant },
  { "distinct", NULL, 34, help_basic },
  { "echo", NULL, 12, help_basic },
  { "eval", NULL, 10, help_basic },
  { "exit", NULL, 22, help_basic },
  { "false", NULL, 40, help_basic },
  { "generic", "Generic Operators", HGENERIC, help_for_category },
  { "help", "Show help", 20, help_variant },
  { "if", NULL, 31, help_basic },
  { "include", NULL, 11, help_basic },
  { "int", NULL, 24, help_basic },
  { "ite", NULL, 30, help_basic },
  { "mk-bv", NULL, 57, help_basic },
  { "mk-tuple", NULL, 35, help_basic },
  { "not", NULL, 43, help_basic },
  { "or", NULL, 41, help_basic },
  { "params", "Parameters", HPARAM, help_for_category },
  { "push", NULL, 6, help_basic },
  { "pop", NULL, 7, help_basic },
  { "real", NULL, 25, help_basic },
  { "reset", NULL, 8, help_basic },
  { "reset-stats", NULL, 17, help_basic },
  { "scalar", NULL, 27, help_basic },
  { "select", NULL, 36, help_basic },
  { "set-param", NULL, 13, help_basic },
  { "set-timeout", NULL, 18, help_basic },
  { "show-model", NULL, 9, help_basic },
  { "show-param", NULL, 14, help_basic },
  { "show-params", NULL, 15, help_basic },
  { "show-stats", NULL, 16, help_basic },
  { "show-timeout", NULL, 19, help_basic },
  { "syntax", syntax_summary, 0, help_special },
  { "true", NULL, 39, help_basic },
  { "tuple", NULL, 28, help_basic },
  { "tuple-update", NULL, 37, help_basic },
  { "types", "Type Constructs", HTYPE, help_for_category },
  { "update", NULL, 38, help_basic },
  { "xor", NULL, 44, help_basic },
  { "^", NULL, 52, help_basic },
  // END MARKER
  { NULL, NULL, 0, NULL },
};


/*
 * Get the index element for topic
 * - return NULL if nothing found
 */
static const help_index_t *help_for_topic(const char *topic) {
  const help_index_t *p;

  for (p = help_index; p->key != NULL; p++) {
    if (strcmp(topic, p->key) == 0) {
      return p;
    }
  }
  return NULL;
}





/*
 * FOR TESTING
 */
void show_help(FILE *f, const char *topic) {
  const help_index_t *index;

  if (topic == NULL) {
    help_for_category(f, NULL, "Command Summary", HCOMMAND);
    fputs("For a list of all help topics: type '(help index)'.\n", f);    
  } else {
    index = help_for_topic(topic);
    if (index != NULL) {
      index->proc(f, topic, index->aux, index->idx);
    } else {
      fputs("\nSorry, nothing relevant\n"
	    "\nTry '(help index)' for a list of help topics\n\n", f);
    }
  }

  fflush(f);
}
