
LETTER	([a-zA-Z])
DIGIT	([0-9])
OPCHAR	(['\.\_])
IDCHAR  ({LETTER}|{DIGIT}|{OPCHAR})
%%

[\n]            { CVCL::parserTemp->lineNum++; }
[ \t\r\f]	{ /* skip whitespace */ }

{DIGIT}+"\."{DIGIT}+ { smtliblval.str = new std::string(smtlibtext); return NUMERAL_TOK; }
{DIGIT}+	{ smtliblval.str = new std::string(smtlibtext); return NUMERAL_TOK;
		}

";"		{ BEGIN COMMENT; }
<COMMENT>"\n"	{ BEGIN INITIAL; /* return to normal mode */
                  CVCL::parserTemp->lineNum++; }
<COMMENT>.	{ /* stay in comment mode */ }

<INITIAL>"\""		{ BEGIN STRING_LITERAL;
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<STRING_LITERAL>"\\".	{ /* escape characters (like \n or \") */
                          _string_lit.insert(_string_lit.end(),
                                             escapeChar(smtlibtext[1])); }
<STRING_LITERAL>"\""	{ BEGIN INITIAL; /* return to normal mode */
			  smtliblval.str = new std::string(_string_lit);
                          return STRING_TOK; }
<STRING_LITERAL>.	{ _string_lit.insert(_string_lit.end(),*smtlibtext); }


<INITIAL>"{"		{ BEGIN USER_VALUE;
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<USER_VALUE>"\\"[{}] { /* escape characters */
                          _string_lit.insert(_string_lit.end(),smtlibtext[1]); }

<USER_VALUE>"}"	        { BEGIN INITIAL; /* return to normal mode */
			  smtliblval.str = new std::string(_string_lit);
                          return USER_VAL_TOK; }

<USER_VALUE>"\n"        { _string_lit.insert(_string_lit.end(),'\n');
                          CVCL::parserTemp->lineNum++; }
<USER_VALUE>.	        { _string_lit.insert(_string_lit.end(),*smtlibtext); }

"true"          { return TRUE_TOK; }
"false"         { return FALSE_TOK; }
"ite"           { return ITE_TOK; }
"not"           { return NOT_TOK; }
"implies"       { return IMPLIES_TOK; }
"if_then_else"  { return IF_THEN_ELSE_TOK; }
"and"           { return AND_TOK; }
"or"            { return OR_TOK; }
"xor"           { return XOR_TOK; }
"iff"           { return IFF_TOK; }
"exists"        { return EXISTS_TOK; }
"forall"        { return FORALL_TOK; }
"let"           { return LET_TOK; }
"flet"          { return FLET_TOK; }
"notes"         { return NOTES_TOK; }
"cvc_command"   { return CVC_COMMAND_TOK; }
"sorts"         { return SORTS_TOK; }
"funs"          { return FUNS_TOK; }
"preds"         { return PREDS_TOK; }
"extensions"    { return EXTENSIONS_TOK; }
"definition"    { return DEFINITION_TOK; }
"axioms"        { return AXIOMS_TOK; }
"logic"         { return LOGIC_TOK; }
"sat"           { return SAT_TOK; }
"unsat"         { return UNSAT_TOK; }
"unknown"       { return UNKNOWN_TOK; }
"assumption"    { return ASSUMPTION_TOK; }
"formula"       { return FORMULA_TOK; }
"status"        { return STATUS_TOK; }
"benchmark"     { return BENCHMARK_TOK; }
"extrasorts"    { return EXTRASORTS_TOK; }
"extrafuns"     { return EXTRAFUNS_TOK; }
"extrapreds"    { return EXTRAPREDS_TOK; }
"language"      { return LANGUAGE_TOK; }
"distinct"      { return DISTINCT_TOK; }
":"             { return COLON_TOK; }
"\["            { return LBRACKET_TOK; }
"\]"            { return RBRACKET_TOK; }
"("             { return LPAREN_TOK; }
")"             { return RPAREN_TOK; }
"$"             { return DOLLAR_TOK; }
"?"             { return QUESTION_TOK; }
[=<>&@#+\-*/%|~]+ { smtliblval.str = new std::string(smtlibtext); return AR_SYMB; }
({LETTER}|("/"))(({IDCHAR})|[\-+/])* {smtliblval.str = new std::string(smtlibtext); return SYM_TOK; }


<<EOF>>         { return EOF_TOK; }

. { smtliberror("Illegal input character."); }
%%

