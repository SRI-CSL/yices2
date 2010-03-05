%{
/*****************************************************************************/
/*!
 * \file smtlib.y
 * 
 * Author: Sergey Berezin, Clark Barrett
 * 
 * Created: Apr 30 2005
 *
 * <hr>
 * Copyright (C) 2004 by the Board of Trustees of Leland Stanford
 * Junior University and by New York University. 
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.  In particular:
 *
 * - The above copyright notice and this permission notice must appear
 * in all copies of the software and related documentation.
 *
 * - THE SOFTWARE IS PROVIDED "AS-IS", WITHOUT ANY WARRANTIES,
 * EXPRESSED OR IMPLIED.  USE IT AT YOUR OWN RISK.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/
/* 
   This file contains the bison code for the parser that reads in CVC
   commands in SMT-LIB language.
*/

#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 10485760

%}

%union {
  std::string *str;
  std::vector<std::string> *strvec;
  CVCL::Expr *node;
  std::vector<CVCL::Expr> *vec;
};


%start cmd

/* strings are for better error messages.  
   "_TOK" is so macros don't conflict with kind names */

%type <vec> bench_attributes sort_symbs fun_symb_decls pred_symb_decls
%type <vec> an_formulas quant_vars an_terms fun_symb
%type <node> benchmark bench_name bench_attribute
%type <node> status fun_symb_decl fun_sig pred_symb_decl pred_sig
%type <node> an_formula quant_var an_atom prop_atom
%type <node> an_term basic_term sort_symb pred_symb
%type <node> var fvar
%type <str> logic_name quant_symb connective user_value attribute annotation
%type <strvec> annotations

%token <str> NUMERAL_TOK
%token <str> SYM_TOK
%token <str> STRING_TOK
%token <str> AR_SYMB
%token <str> USER_VAL_TOK
%token TRUE_TOK
%token FALSE_TOK
%token ITE_TOK
%token NOT_TOK
%token IMPLIES_TOK
%token IF_THEN_ELSE_TOK
%token AND_TOK
%token OR_TOK
%token XOR_TOK
%token IFF_TOK
%token EXISTS_TOK
%token FORALL_TOK
%token LET_TOK
%token FLET_TOK
%token NOTES_TOK
%token CVC_COMMAND_TOK
%token SORTS_TOK
%token FUNS_TOK
%token PREDS_TOK
%token EXTENSIONS_TOK
%token DEFINITION_TOK
%token AXIOMS_TOK
%token LOGIC_TOK
%token COLON_TOK
%token LBRACKET_TOK
%token RBRACKET_TOK
%token LPAREN_TOK
%token RPAREN_TOK
%token SAT_TOK
%token UNSAT_TOK
%token UNKNOWN_TOK
%token ASSUMPTION_TOK
%token FORMULA_TOK
%token STATUS_TOK
%token BENCHMARK_TOK
%token EXTRASORTS_TOK
%token EXTRAFUNS_TOK
%token EXTRAPREDS_TOK
%token LANGUAGE_TOK
%token DOLLAR_TOK
%token QUESTION_TOK
%token DISTINCT_TOK
%token SEMICOLON_TOK
%token EOF_TOK

%%

cmd:
    benchmark
;

benchmark:
    LPAREN_TOK BENCHMARK_TOK bench_name bench_attributes RPAREN_TOK
  | EOF_TOK
;

bench_name:
    SYM_TOK
;

bench_attributes:
    bench_attribute
  | bench_attributes bench_attribute
;

bench_attribute:
    COLON_TOK ASSUMPTION_TOK an_formula
  | COLON_TOK FORMULA_TOK an_formula 
  | COLON_TOK STATUS_TOK status 
  | COLON_TOK LOGIC_TOK logic_name 
  | COLON_TOK EXTRASORTS_TOK LPAREN_TOK sort_symbs RPAREN_TOK
  | COLON_TOK EXTRAFUNS_TOK LPAREN_TOK fun_symb_decls RPAREN_TOK
  | COLON_TOK EXTRAPREDS_TOK LPAREN_TOK pred_symb_decls RPAREN_TOK
  | COLON_TOK NOTES_TOK STRING_TOK
  | COLON_TOK CVC_COMMAND_TOK STRING_TOK
  | annotation
;

logic_name:
    SYM_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
  | SYM_TOK
;

status:
    SAT_TOK
  | UNSAT_TOK
  | UNKNOWN_TOK
;

sort_symbs:
    sort_symb 
  | sort_symbs sort_symb
;

fun_symb_decls:
    fun_symb_decl
  | fun_symb_decls fun_symb_decl
;

fun_symb_decl:
    LPAREN_TOK fun_sig annotations RPAREN_TOK
  | LPAREN_TOK fun_sig RPAREN_TOK
;

fun_sig:
    fun_symb sort_symbs
;

pred_symb_decls:
    pred_symb_decl
  | pred_symb_decls pred_symb_decl
;

pred_symb_decl:
    LPAREN_TOK pred_sig annotations RPAREN_TOK
  | LPAREN_TOK pred_sig RPAREN_TOK
;

pred_sig:
    pred_symb sort_symbs
  | pred_symb
;

an_formulas:
    an_formula
  | an_formulas an_formula
;

an_formula:
    an_atom
  | LPAREN_TOK connective an_formulas annotations RPAREN_TOK
  | LPAREN_TOK connective an_formulas RPAREN_TOK
  | LPAREN_TOK quant_symb quant_vars an_formula annotations RPAREN_TOK
  | LPAREN_TOK quant_symb quant_vars an_formula RPAREN_TOK
  | LPAREN_TOK LET_TOK LPAREN_TOK var an_term RPAREN_TOK an_formula annotations RPAREN_TOK
  | LPAREN_TOK LET_TOK LPAREN_TOK var an_term RPAREN_TOK an_formula RPAREN_TOK
  | LPAREN_TOK FLET_TOK LPAREN_TOK fvar an_formula RPAREN_TOK an_formula annotations RPAREN_TOK
  | LPAREN_TOK FLET_TOK LPAREN_TOK fvar an_formula RPAREN_TOK an_formula RPAREN_TOK
;

quant_vars:
    quant_var
  | quant_vars quant_var
;

quant_var: 
    LPAREN_TOK var sort_symb RPAREN_TOK
;

quant_symb:
    EXISTS_TOK
  | FORALL_TOK
;

connective:
    NOT_TOK
  | IMPLIES_TOK
  | IF_THEN_ELSE_TOK
  | AND_TOK
  | OR_TOK
  | XOR_TOK
  | IFF_TOK
;

an_atom:
    prop_atom 
  | LPAREN_TOK prop_atom annotations RPAREN_TOK 
  | LPAREN_TOK pred_symb an_terms annotations RPAREN_TOK
  | LPAREN_TOK pred_symb an_terms RPAREN_TOK
  | LPAREN_TOK DISTINCT_TOK an_terms annotations RPAREN_TOK
  | LPAREN_TOK DISTINCT_TOK an_terms RPAREN_TOK
;

prop_atom:
    TRUE_TOK
  | FALSE_TOK
  | fvar
  | pred_symb 
;  

an_terms:
    an_term
  | an_terms an_term
;

an_term:
    basic_term 
  | LPAREN_TOK basic_term annotations RPAREN_TOK 
  | LPAREN_TOK fun_symb an_terms annotations RPAREN_TOK
  | LPAREN_TOK fun_symb an_terms RPAREN_TOK
  | LPAREN_TOK ITE_TOK an_formula an_term an_term annotations RPAREN_TOK
  | LPAREN_TOK ITE_TOK an_formula an_term an_term RPAREN_TOK
;

basic_term:
    var
  | fun_symb 
;

annotations:
    annotation
  | annotations annotation
  ;
  
annotation:
    attribute 
  | attribute user_value 
;

user_value:
    USER_VAL_TOK
;

sort_symb:
    SYM_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
  | SYM_TOK 
;

pred_symb:
    SYM_TOK // bv and other stuff
  | AR_SYMB // arithmetic comparisons
;

fun_symb: 
    SYM_TOK LBRACKET_TOK NUMERAL_TOK COLON_TOK NUMERAL_TOK RBRACKET_TOK  // extract
  | SYM_TOK  // other built-in and primitive synbols
  | AR_SYMB  // arithmetic 
  | NUMERAL_TOK
;

attribute:
    COLON_TOK SYM_TOK
;

var:
    QUESTION_TOK SYM_TOK
;

fvar:
    DOLLAR_TOK SYM_TOK
;

%%
