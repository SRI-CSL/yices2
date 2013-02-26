%option noyywrap
%option noinput
%option nounput

%{
#include "string_buffers.h"
#include "hash.h"
static string_buffer_t lex_string_buffer;
const char *cached_string(const char *p);
int lineno = 1;
%}

%x comment
%x string
%x symbol

SYMBOL	[-a-zA-Z+/*=%?!.$_~&^<>@][-0-9a-zA-Z+/*=%?!.$_~&^<>@]*
KEYWORD	:[-0-9a-zA-Z+/*=%?!.$_~&^<>@]+

%%

[ \t\r]			{ ; }
\n			{ lineno++; prompt(); }
[()!_]			{ prompt_level = 1; return *yytext; }
";"			{ BEGIN comment; }
<comment>.		{ ; }
<comment>\n		{ lineno++; BEGIN 0; prompt(); }

"as"			{ return AS; }
"assert"		{ return ASSERT; }
"check-sat"		{ return CHECK_SAT; }
"declare-fun"		{ return DECLARE_FUN; }
"declare-sort"		{ return DECLARE_SORT; }
"define-fun"		{ return DEFINE_FUN; }
"define-sort"		{ return DEFINE_SORT; }
"exists"		{ return EXISTS; }
"exit"			{ return EXIT; }
"forall"		{ return FORALL; }
"get-assertions"	{ return GET_ASSERTIONS; }
"get-assignment"	{ return GET_ASSIGNMENT; }
"get-info"		{ return GET_INFO; }
"get-option"		{ return GET_OPTION; }
"get-proof"		{ return GET_PROOF; }
"get-unsat-core"	{ return GET_UNSAT_CORE; }
"get-value"		{ return GET_VALUE; }
"let"			{ return LET; }
"pop"			{ return POP; }
"push"			{ return PUSH; }
"set-info"		{ return SET_INFO; }
"set-logic"		{ return SET_LOGIC; }
"set-option"		{ return SET_OPTION; }

[-+]?[0-9]+		{ yylval.num.term = yices_parse_rational(yytext);
			  yylval.num.val = atoi(yytext);
			  return NUMERAL; }
[-+]?[0-9]+\.[0-9]*	{ yylval.term = yices_parse_float(yytext);
			  return DECIMAL; }
"#x"[0-9a-fA-F]+	{ yylval.term = yices_parse_bvhex(yytext+2);
			  return HEX; }
"#b"[01]+		{ yylval.term = yices_parse_bvbin(yytext+2);
			  return BINARY; }

{SYMBOL}	{ yylval.str = cached_string(yytext);
		  return SYMBOL; }
"|"		{ string_buffer_reset(&lex_string_buffer);
		  BEGIN symbol; }
<symbol>"|"	{ BEGIN 0;
		  string_buffer_close(&lex_string_buffer);
		  yylval.str = cached_string(lex_string_buffer.data);
		  return SYMBOL; }
<symbol>.	{ string_buffer_append_char(&lex_string_buffer, *yytext); }
<symbol>\n	{ string_buffer_append_char(&lex_string_buffer, *yytext);
		  lineno++; prompt(); }
{KEYWORD}	{ yylval.str = cached_string(yytext+1);
		  return KEYWORD; }

\"		{ string_buffer_reset(&lex_string_buffer);
		  BEGIN string; }
<string>\"	{ BEGIN 0;
		  string_buffer_close(&lex_string_buffer);
		  yylval.str = cached_string(lex_string_buffer.data);
		  return STRING; }
<string>\\.	{ string_buffer_append_char(&lex_string_buffer, yytext[1]); }
<string>.	{ string_buffer_append_char(&lex_string_buffer, *yytext); }
<string>\n	{ string_buffer_append_char(&lex_string_buffer, *yytext);
		  lineno++; prompt(); }

.		{ if (*yytext > 32 && *yytext < 127)
		    fprintf(stderr, "spurious character '%c' in input\n",
			    *yytext);
		  else
		    fprintf(stderr, "spurious character '\\x%x' in input\n",
			    *yytext); }

<<EOF>>		{ yypop_buffer_state();
		  if (!YY_CURRENT_BUFFER) yyterminate(); }

%%

const char *cached_string(const char *p)
{
    static hash_table *string_table;
    hash_lookup_cache	cache;
    const char *rv;
    if (!string_table)
	string_table = new_hashset(strhash, strcmp, 100);
    rv = hashset_lookup(string_table, p, &cache);
    if (!rv) {
	int len = strlen(p) + 1;
	rv = safe_malloc(len);
	memcpy((char *)rv, p, len);
	hashset_insert(string_table, rv, &cache); }
    return rv;
}
