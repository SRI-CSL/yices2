/*
 * Grammar for the yices language (test)
 */

%{
extern int yylex(void);
extern void yyerror(char const *);
%}

%token TK_LP 
%token TK_RP
%token TK_COLON_COLON
%token TK_EOS
%token TK_STRING
%token TK_NUM_RATIONAL
%token TK_NUM_FLOAT
%token TK_BV_CONSTANT
%token TK_HEX_CONSTANT
%token TK_SYMBOL
 
%token TK_BOOL
%token TK_INT
%token TK_REAL
%token TK_BITVECTOR
%token TK_SCALAR
%token TK_TUPLE
%token TK_ARROW
 
%token TK_TRUE
%token TK_FALSE

%token TK_IF
%token TK_ITE
%token TK_EQ
%token TK_DISEQ
%token TK_OR
%token TK_AND
%token TK_NOT
%token TK_XOR
%token TK_IFF
%token TK_IMPLIES
%token TK_MK_TUPLE
%token TK_SELECT
%token TK_ADD
%token TK_SUB
%token TK_MUL
%token TK_DIV
%token TK_LT
%token TK_LE
%token TK_GT
%token TK_GE
%token TK_MK_BV
%token TK_BV_ADD
%token TK_BV_SUB
%token TK_BV_MUL
%token TK_BV_NEG
%token TK_BV_NOT
%token TK_BV_AND
%token TK_BV_OR
%token TK_BV_XOR
%token TK_BV_NAND
%token TK_BV_NOR
%token TK_BV_XNOR
%token TK_BV_SHIFT_LEFT0
%token TK_BV_SHIFT_LEFT1
%token TK_BV_SHIFT_RIGHT0
%token TK_BV_SHIFT_RIGHT1
%token TK_BV_ASHIFT_RIGHT
%token TK_BV_ROTATE_LEFT
%token TK_BV_ROTATE_RIGHT
%token TK_BV_EXTRACT
%token TK_BV_CONCAT
%token TK_BV_REPEAT
%token TK_BV_GE
%token TK_BV_GT
%token TK_BV_LE
%token TK_BV_LT
%token TK_BV_SGE
%token TK_BV_SGT
%token TK_BV_SLE
%token TK_BV_SLT

%token TK_LET
%token TK_FORALL
%token TK_EXISTS
%token TK_UPDATE

%token TK_DEFINE_TYPE
%token TK_DEFINE
%token TK_ASSERT
%token TK_CHECK
%token TK_ECHO  
%token TK_INCLUDE
%token TK_EXIT


%%
command: TK_EOS
       | define_type
       | define_term
       | assert
       | check
       | echo
       | include
       | exit
;

assert: TK_LP TK_ASSERT expression TK_RP
;

check: TK_LP TK_CHECK TK_RP
;

echo: TK_LP TK_ECHO TK_STRING TK_RP
;

include: TK_LP TK_INCLUDE TK_STRING TK_RP
;

exit: TK_LP TK_EXIT TK_RP
;


define_type: TK_LP TK_DEFINE_TYPE TK_SYMBOL deftype_or_empty TK_RP
;

deftype_or_empty: /* empty */
       | type
       | scalar_typedef
;

scalar_typedef: TK_LP TK_SCALAR list_of_symbols TK_RP
;

list_of_symbols: TK_SYMBOL | list_of_symbols TK_SYMBOL
;

type: TK_BOOL 
       | TK_INT 
       | TK_REAL
       | TK_LP TK_BITVECTOR TK_NUM_RATIONAL TK_RP 
       | TK_LP TK_TUPLE list_of_types TK_RP
       | TK_LP TK_ARROW list_of_types type TK_RP
;

list_of_types: type | list_of_types type 
;


define_term: TK_LP TK_DEFINE TK_SYMBOL TK_COLON_COLON type expression_or_empty TK_RP
;

expression_or_empty: /* empty */
      | expression
;

expression: TK_TRUE | TK_FALSE | TK_NUM_RATIONAL | TK_NUM_FLOAT 
      | TK_BV_CONSTANT | TK_HEX_CONSTANT | TK_SYMBOL
      | TK_LP TK_FORALL TK_LP list_of_decls TK_RP expression TK_RP
      | TK_LP TK_EXISTS TK_LP list_of_decls TK_RP expression TK_RP
      | TK_LP TK_LET TK_LP list_of_bindings TK_RP expression TK_RP
      | TK_LP TK_UPDATE expression TK_LP list_of_expressions TK_RP expression TK_RP
      | TK_LP function list_of_expressions TK_RP
;

list_of_decls: decl | list_of_decls decl
;

decl: TK_SYMBOL TK_COLON_COLON type
;

list_of_bindings: binding | list_of_bindings binding
;

binding: TK_LP TK_SYMBOL expression TK_RP
;

list_of_expressions: expression | list_of_expressions expression
;

function: expression |
  TK_IF |
  TK_ITE |
  TK_EQ |
  TK_DISEQ |
  TK_OR |
  TK_AND |
  TK_NOT |
  TK_XOR |
  TK_IFF |
  TK_IMPLIES |
  TK_MK_TUPLE |
  TK_SELECT |
  TK_ADD |
  TK_SUB |
  TK_MUL |
  TK_DIV |
  TK_LT |
  TK_LE |
  TK_GT |
  TK_GE |
  TK_MK_BV |
  TK_BV_ADD |
  TK_BV_SUB |
  TK_BV_MUL |
  TK_BV_NEG |
  TK_BV_NOT |
  TK_BV_AND |
  TK_BV_OR |
  TK_BV_XOR |
  TK_BV_NAND |
  TK_BV_NOR |
  TK_BV_XNOR |
  TK_BV_SHIFT_LEFT0 |
  TK_BV_SHIFT_LEFT1 |
  TK_BV_SHIFT_RIGHT0 |
  TK_BV_SHIFT_RIGHT1 |
  TK_BV_ASHIFT_RIGHT |
  TK_BV_ROTATE_LEFT |
  TK_BV_ROTATE_RIGHT |
  TK_BV_EXTRACT |
  TK_BV_CONCAT |
  TK_BV_REPEAT |
  TK_BV_GE |
  TK_BV_GT |
  TK_BV_LE |
  TK_BV_LT |
  TK_BV_SGE |
  TK_BV_SGT |
  TK_BV_SLE |
  TK_BV_SLT
;

%%
