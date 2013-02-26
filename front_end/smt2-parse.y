%{
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <assert.h>
#include "yices.h"
#include "memalloc.h"

#include "cputime.h"
#include "memsize.h"
#include "smt2-eval.h"

/*
 * Functions declared in yices_extensions.h
 * We can't use #include "yices_externsionas.h" 
 & here because of a conflict in type definition
 * (value_t) is defined twice.
 */ 
extern void yices_print_presearch_stats(FILE *f, context_t *ctx);
extern void yices_show_statistics(FILE *f, context_t *ctx);

#define YY_DECL static int yylex()
YY_DECL;
extern void yyerror(const char *fmt, ...);
#define YYMAXDEPTH	10000000

typedef struct {
    const char	*name;
    type_t	type;
} var_t;

typedef struct {
    const char	*name;
    value_t	val;
} bind_t;

DECLARE_VECTOR2(string, const char *)
DECLARE_VECTOR(bind_t)
DECLARE_VECTOR(term_t)
DECLARE_VECTOR(type_t)
DECLARE_VECTOR(value_t)
DECLARE_VECTOR(var_t)
DECLARE_VECTOR(int)

static int exit_code = 0;
static const char *status_needed = 0;
static int prompt_level = 0;
static void prompt();

void set_logic(const char *name);
void set_option(const char *name, value_t val);
void set_info(const char *name, value_t val);
void declare_sort(const char *name, int params);
void define_sort(const char *name, int ac, const char **av, type_t as);
void declare_fun(const char *name, int ac, type_t *av, type_t ret);
void define_fun(const char *name, int ac, term_t *av, type_t ret, value_t body);
void do_push(int);
void do_pop(int);
void do_assert(value_t);
void check_sat();
type_t parameterized_sort(const char *, int, type_t *);
void declare_bind_names(int count, bind_t *b);
void declare_var_names(VECTOR(term_t) *out, int count, var_t *b);
void undeclare_bind_names(int count, bind_t *b);
void undeclare_var_names(int count, var_t *b);

%}

%union {
    const char 		*str;
    VECTOR(string)	strings;
    term_t		term;
    VECTOR(term_t)	terms;
    type_t		type;
    VECTOR(type_t)	types;
    value_t		value;
    VECTOR(value_t)	values;
    var_t		var;
    VECTOR(var_t)	vars;
    bind_t		bind;
    VECTOR(bind_t)	binds;
    VECTOR(int)		indexes;
    struct {
	term_t		term;
	int		val;
    }			num;
}

%token AS ASSERT CHECK_SAT DECLARE_FUN DECLARE_SORT DEFINE_FUN
%token DEFINE_SORT EXISTS EXIT FORALL GET_ASSERTIONS GET_ASSIGNMENT
%token GET_INFO GET_OPTION GET_PROOF GET_UNSAT_CORE GET_VALUE LET
%token POP PUSH SET_INFO SET_LOGIC SET_OPTION

%token <str> SYMBOL
%token <str> KEYWORD
%token <num> NUMERAL
%token <term> DECIMAL
%token <term> HEX
%token <term> BINARY
%token <str> STRING

%type <bind> bind attrib
%type <binds> binds attributes
%type <strings> symbols
%type <values> terms values
%type <value> term qual_identifier value
%type <type> sort
%type <types> sorts
%type <vars> vars
%type <var> var
%type <indexes> indexes

%destructor { VECTOR_free($$); } symbols sorts vars binds attributes indexes

%%

input	: /* empty */
	| input command
	    { prompt_level = 0; }
;

command : '(' SET_LOGIC SYMBOL ')'
	    { set_logic($3); }
	| '(' SET_OPTION attrib ')'
	    { set_option($3.name, $3.val); }
	| '(' SET_INFO attrib ')'
	    { set_info($3.name, $3.val); }
	| '(' DECLARE_SORT SYMBOL NUMERAL ')'
	    { declare_sort($3, $4.val); }
	| '(' DEFINE_SORT SYMBOL '(' symbols ')' sort ')'
	    { define_sort($3, $5.size, $5.data, $7);
	      VECTOR_free($5); }
	| '(' DECLARE_FUN SYMBOL '(' sorts ')' sort ')'
	    { declare_fun($3, $5.size, $5.data, $7);
	      VECTOR_free($5); }
	| '(' DEFINE_FUN SYMBOL '(' vars
	    { VECTOR_init($<terms>$); 
	      declare_var_names(&$<terms>$, $5.size, $5.data); }
	  ')' sort term ')'
	    { define_fun($3, $5.size, $<terms>6.data, $8, $9);
	      undeclare_var_names($5.size, $5.data);
	      VECTOR_free($5);
	      VECTOR_free($<terms>6); }
	| '(' PUSH NUMERAL ')'
	    { do_push($3.val); }
	| '(' POP NUMERAL ')'
	    { do_pop($3.val); }
	| '(' ASSERT term ')'
	    { do_assert($3); }
	| '(' CHECK_SAT ')'
	    { check_sat(); }
	| '(' GET_ASSERTIONS ')'
	    { assert(0); }
	| '(' GET_PROOF ')'
	    { assert(0); }
	| '(' GET_UNSAT_CORE ')'
	    { assert(0); }
	| '(' GET_VALUE '(' terms ')' ')'
	    { assert(0);
	      VECTOR_free($4); }
	| '(' GET_ASSIGNMENT ')'
	    { assert(0); }
	| '(' GET_OPTION KEYWORD ')'
	    { assert(0); }
	| '(' GET_INFO KEYWORD ')'
	    { assert(0); }
	| '(' EXIT ')'
	    { exit(exit_code); }
	| '(' error ')'
	| error
;

symbols	: /*empty*/	 { VECTOR_init($$); }
	| symbols SYMBOL { VECTOR_add($1, $2); $$ = $1; }
	| symbols error	 { $$ = $1; }
	;

sorts	: /*empty*/	{ VECTOR_init($$); }
	| sorts sort	{ VECTOR_add($1, $2); $$ = $1; }
	| sorts error	{ $$ = $1; }
	;
sort	: SYMBOL
	    { if (($$ = yices_get_type_by_name($1)) == NULL_TYPE)
		yyerror("not a sort symbol: %s", $1); }
	| '(' SYMBOL sorts ')'
	    { $$ = parameterized_sort($2, $3.size, $3.data);
	      VECTOR_free($3); }
	| '(' '_' SYMBOL indexes ')'
	    { $$ = indexed_type($3, $4.size, $4.data);
	      VECTOR_free($4); }
	;
    
vars	: /*empty*/	{ VECTOR_init($$); }
	| vars var	{ VECTOR_add($1, $2); $$ = $1; }
	| vars error	{ $$ = $1; }
	;
var	: '(' SYMBOL sort ')'	{ $$.name = $2; $$.type = $3; }
	| '(' error ')'		{ $$.name = 0; $$.type = NULL_TYPE; }
	;

binds	: /*empty*/	{ VECTOR_init($$); }
	| binds bind	{ VECTOR_add($1, $2); $$ = $1; }
	;
bind	: '(' SYMBOL term ')'	{ $$.name = $2; $$.val = $3; }
	| '(' error ')'		{ $$.name = 0; $$.val = UNKNOWNval(); }
	;

terms	: term		{ VECTOR_init($$); VECTOR_add($$, $1); }
	| terms term	{ VECTOR_add($1, $2); $$ = $1; }
	;
term	: NUMERAL	{ $$.tag = vtTERM; $$.v.term = $1.term; }
	| DECIMAL	{ $$.tag = vtTERM; $$.v.term = $1; }
	| HEX		{ $$.tag = vtTERM; $$.v.term = $1; }
	| BINARY	{ $$.tag = vtTERM; $$.v.term = $1; }
	| STRING	{ $$.tag = vtSTRING; $$.v.str = $1; }
	| qual_identifier { $$ = $1; }
	| '(' qual_identifier ')'
	    { $$ = eval_sexpr($2, 0, 0); }
	| '(' qual_identifier terms ')'
	    { $$ = eval_sexpr($2, $3.size, $3.data);
	      VECTOR_free($3); }
	| '(' LET '(' binds 
	    { declare_bind_names($4.size, $4.data); }
	  ')' term ')'
	    { undeclare_bind_names($4.size, $4.data);
	      $$ = $7;
	      VECTOR_free($4); }
	| '(' FORALL '(' vars
	    { VECTOR_init($<terms>$); 
	      declare_var_names(&$<terms>$, $4.size, $4.data); }
	  ')' term ')'
	    { $$.tag = vtTERM;
	      assert($7.tag == vtTERM);
	      $$.v.term = yices_forall($4.size, $<terms>5.data, $7.v.term);
	      undeclare_var_names($4.size, $4.data);
	      VECTOR_free($4);
	      VECTOR_free($<terms>5); }
	| '(' EXISTS '(' vars
	    { VECTOR_init($<terms>$); 
	      declare_var_names(&$<terms>$, $4.size, $4.data); }
	  ')' term ')'
	    { $$.tag = vtTERM;
	      assert($7.tag == vtTERM);
	      $$.v.term = yices_exists($4.size, $<terms>5.data, $7.v.term);
	      undeclare_var_names($4.size, $4.data);
	      VECTOR_free($4);
	      VECTOR_free($<terms>5); }
	| '(' '!' term attributes ')'
	    { $$ = $3;
	      yyerror("FIXME -- ignoring attributes with !");
	      VECTOR_free($4); }
	| '(' error ')'
	    { $$ = UNKNOWNval(); }
	;

qual_identifier
	: SYMBOL {
	    if (($$.v.term = yices_get_term_by_name($1)) != NULL_TERM)
		$$.tag = vtTERM;
	    else {
		$$.tag = vtSYMBOL; $$.v.str = $1; } }
	| '(' AS SYMBOL sort ')'
	    { yyerror("FIXME -- AS not implemented");
	      $$.tag = vtSYMBOL; $$.v.str = $3; }
	| '(' '_' SYMBOL indexes ')'
	    { $$ = indexed_value($3, $4.size, $4.data);
	      VECTOR_free($4); }
	;

indexes	: NUMERAL		{ VECTOR_init($$); VECTOR_add($$, $1.val); }
	| indexes NUMERAL	{ VECTOR_add($1, $2.val); $$ = $1; }
	;

attributes: attrib		{ VECTOR_init($$); VECTOR_add($$, $1); }
	| attributes attrib	{ VECTOR_add($1, $2); $$ = $1; }
	;
attrib	: KEYWORD		{ $$.name = $1; $$.val = UNKNOWNval(); }
	| KEYWORD value		{ $$.name = $1; $$.val = $2; }
	;

values	: /* empty */		{ VECTOR_init($$); }
	| values value		{ VECTOR_add($1, $2); $$ = $1; }
	| values KEYWORD	{ VECTOR_add($1, STRINGval($2)); $$ = $1; }
	;

value	: NUMERAL	{ $$.tag = vtTERM; $$.v.term = $1.term; }
	| DECIMAL	{ $$.tag = vtTERM; $$.v.term = $1; }
	| HEX		{ $$.tag = vtTERM; $$.v.term = $1; }
	| BINARY	{ $$.tag = vtTERM; $$.v.term = $1; }
	| STRING	{ $$.tag = vtSTRING; $$.v.str = $1; }
	| SYMBOL	{ $$.tag = vtSYMBOL; $$.v.str = $1; }
	| '(' values ')'
	    { $$ = eval_sexpr($2.data[0], $2.size-1, $2.data+1);
	      VECTOR_free($2); }
	| '(' error ')'
	    { $$ = UNKNOWNval(); }
	;

%%

#include "smt2-lex.c"

void yyerror(const char *fmt, ...)
{
    va_list	args;
    if (!YY_CURRENT_BUFFER->yy_is_interactive)
	fprintf(stderr, "%d: ", lineno);
    va_start(args, fmt);
    vfprintf(stderr, fmt, args);
    va_end(args);
    fprintf(stderr, "\n");
    exit_code = 2;
}

static ctx_config_t *config = 0;
static context_t *context = 0;
static VECTOR(term_t) assertions;

int main(int ac, char **av)
{
  FILE *fp = 0;
  int code;

  VECTOR_init(assertions);
  while (*++av) {
#if YYDEBUG
    if (!strcmp(*av, "-d"))
      yydebug = 1;
    else
#endif
    if (fp)
      fprintf(stderr, "Only one source on command line supported\n");
    else if (!(fp = fopen(*av, "r")))
      fprintf(stderr, "Can't open %s\n", *av);
  }
  yy_switch_to_buffer(yy_create_buffer(fp ? fp : stdin, YY_BUF_SIZE));
  prompt();
  yices_init();
  eval_init();
  code = yyparse();

  VECTOR_free(assertions);
  
  return code;
}

static void prompt()
{
  if (YY_CURRENT_BUFFER->yy_is_interactive) {
    printf("%s> ", prompt_level ? "..." : "yices-smt2");
    fflush(stdout);
  }
}

void set_logic(const char *name)
{
  if (config) {
    yyerror("already have logic");
  } else {
    config = yices_new_config();
    if (yices_default_config_for_logic(config, name)) {
      yyerror("Unknown/unsupported logic %s", name);
      exit(3); 
    }
  }

  if (config) {
    yices_set_config(config, "mode", "one-shot");
    context = yices_new_context(config);
    yices_context_enable_option(context, "flatten");    // BD: Force flattening
  }  

  if (yices_error_code()) {
    yyerror("yices error:");
    yices_print_error(stderr);
    yices_clear_error(); 
  }
}

void set_option(const char *name, value_t val)
{
}

void set_info(const char *name, value_t val)
{
    if (!strcmp(name, "status")) {
	assert(val.tag == vtSYMBOL || val.tag == vtSTRING);
	if (exit_code == 0 && strcmp(val.v.str, "unknown")) {
	    exit_code = 1;
	    status_needed = val.v.str; } }
    // FIXME -- ignore all other info?
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void declare_sort(const char *name, int params)
{
    if (!config) {
	yyerror("no logic set");
	return; }
    type_t n = yices_new_uninterpreted_type();
    yices_set_type_name(n, name);
    if (params)
	yyerror("FIXME -- parameterized types not supported");
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void define_sort(const char *name, int ac, const char **av, type_t as)
{
    yyerror("FIXME -- define-sort not implemented");
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void declare_fun(const char *name, int ac, type_t *av, type_t ret)
{
    type_t t = ret;
    term_t n;
    if (!config) {
	yyerror("no logic set");
	return; }
    if (ac > 0)
	t = yices_function_type(ac, av, ret);
    n = yices_new_uninterpreted_term(t);
    yices_set_term_name(n, name);
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void define_fun(const char *name, int ac, term_t *av, type_t ret, value_t body)
{
    if (!config) {
	yyerror("no logic set");
	return; }
    if (body.tag == vtSYMBOL) {
	body.v.term = yices_get_term_by_name(body.v.str);
	body.tag = vtTERM; }
    if (body.tag != vtTERM || body.v.term == NULL_TERM) {
	yyerror("FIXME -- invalid body in define-fun %s", name);
	return; }
    /* FIXME -- should check body to ensure it matches the return type?  We're
     * FIXME -- otherwise not really using the return type at all... */
    if (ac > 0) {
	body.v.term = yices_lambda(ac, av, body.v.term); }
    yices_set_term_name(body.v.term, name);
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void do_push(int cnt)
{
    if (!config) {
	yyerror("no logic set");
	return; }
    while(cnt-- > 0)
	if (yices_push(context))
	    yyerror("FIXME -- push failed");
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void do_pop(int cnt)
{
    if (!config) {
	yyerror("no logic set");
	return; }
    while(cnt-- > 0)
	if (yices_pop(context))
	    yyerror("FIXME -- pop failed");
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

#define DELAY_ASSERTIONS 1

void do_assert(value_t t)
{
  if (!config) {
    yyerror("no logic set");
    return; }
  if (t.tag != vtTERM) {
    fprintf(stderr, "%d:FIXME -- assert of non-term: ", lineno);
    print_value(stderr, t);
    fprintf(stderr, "\n");
  } else {
#if DELAY_ASSERTIONS
    // delay assertion: store it in the assertions vector
    VECTOR_add(assertions, t.v.term);
#else
    // process immediately
    if (yices_assert_formula(context, t.v.term)) {
      fprintf(stderr, "%d:FIXME -- failed assert: ", lineno);
      print_value(stderr, t);
      fprintf(stderr, "\n"); 
    }
    if (yices_error_code()) {
      yyerror("yices error:");
      yices_print_error(stderr);
      yices_clear_error(); 
    }
#endif
  }
}

void check_sat()
{
  if (!config) {
    yyerror("no logic set");
    return; }
  if (exit_code == 2 && !YY_CURRENT_BUFFER->yy_is_interactive)
    return; /* don't bother if there were parse errors and not interactive*/

#if DELAY_ASSERTIONS
  // process the delayed assertions
  if (assertions.size > 0) {
    int code = yices_assert_formulas(context, assertions.size, assertions.data);
    if (code < 0) {
      yyerror("Error asserting formulas:");
      yices_print_error(stderr);
      exit(2);
    } 
    assertions.size = 0;
  }
#endif

  // output run time + stat summary
  double construction_time = get_cpu_time();
  double mem_used = mem_size() / (1024 * 1024);
  fprintf(stderr, "Construction time: %.4f s\n", construction_time);
  fprintf(stderr, "Memory used: %.2f MB\n\n", mem_used);
  yices_print_presearch_stats(stderr, context);
  fflush(stderr);

  // print the internalization vectors
  //  pp_context(stderr, context);

  smt_status_t rv = yices_check_context(context, 0);
  //    smt_status_t rv = STATUS_UNKNOWN; // to benchmark parsing/internalization
  switch(rv) {
  case STATUS_SAT:
    printf("sat\n");
    if (status_needed && !strcmp(status_needed, "sat") && exit_code == 1)
      exit_code = 0;
    break;
  case STATUS_UNSAT:
    printf("unsat\n");
    if (status_needed && !strcmp(status_needed, "unsat") && exit_code == 1)
      exit_code = 0;
    break;
  case STATUS_UNKNOWN:
    printf("unknown\n");
    break;
  case STATUS_INTERRUPTED:
    printf("interrupted\n");
    break;
  case STATUS_ERROR:
    printf("error\n");
    break;
  default: 
    printf("unknown code %d\n", rv); 
    break;
  }
  if (yices_error_code()) {
    yyerror("yices error:");
    yices_print_error(stderr);
    yices_clear_error(); 
  }
}

type_t parameterized_sort(const char *name, int ac, type_t *av)
{
    type_t rv;
    if (ac == 2 && !strcmp(name, "Array"))
	return yices_function_type(1, av, av[1]);
    yyerror("FIXME -- parameterized sorts not supported");
    if ((rv = yices_get_type_by_name(name)) == NULL_TYPE)
	yyerror("not a sort symbol: %s", name);
    return rv;
}

void declare_bind_names(int count, bind_t *b)
{
    while(--count >= 0) {
	if (b->val.tag != vtTERM) {
	    fprintf(stderr, "%d:FIXME -- bind %s of non-term: ", lineno, b->name);
	    print_value(stderr, b->val);
	    fprintf(stderr, "\n"); }
	yices_set_term_name(b->val.v.term, b->name);
	b++; }
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void declare_var_names(VECTOR(term_t) *out, int count, var_t *v)
{
    while(--count >= 0) {
	term_t n = yices_new_variable(v->type);
	yices_set_term_name(n, v->name);
	VECTOR_add(*out, n);
	v++; }
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void undeclare_bind_names(int count, bind_t *b)
{
    while(--count >= 0) {
	yices_remove_term_name(b->name);
	b++; }
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}

void undeclare_var_names(int count, var_t *v)
{
    while(--count >= 0) {
	yices_remove_term_name(v->name);
	v++; }
    if (yices_error_code()) {
	yyerror("yices error:");
	yices_print_error(stderr);
	yices_clear_error(); }
}
