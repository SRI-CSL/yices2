/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -L ANSI-C -W yices_kw --output-file=frontend/yices/yices_hash_keywords.h --lookup-function-name=in_yices_kw frontend/yices/yices_keywords.txt  */
/* Computed positions: -k'1,4-5,$' */

#if !((' ' == 32) && ('!' == 33) && ('"' == 34) && ('#' == 35) \
      && ('%' == 37) && ('&' == 38) && ('\'' == 39) && ('(' == 40) \
      && (')' == 41) && ('*' == 42) && ('+' == 43) && (',' == 44) \
      && ('-' == 45) && ('.' == 46) && ('/' == 47) && ('0' == 48) \
      && ('1' == 49) && ('2' == 50) && ('3' == 51) && ('4' == 52) \
      && ('5' == 53) && ('6' == 54) && ('7' == 55) && ('8' == 56) \
      && ('9' == 57) && (':' == 58) && (';' == 59) && ('<' == 60) \
      && ('=' == 61) && ('>' == 62) && ('?' == 63) && ('A' == 65) \
      && ('B' == 66) && ('C' == 67) && ('D' == 68) && ('E' == 69) \
      && ('F' == 70) && ('G' == 71) && ('H' == 72) && ('I' == 73) \
      && ('J' == 74) && ('K' == 75) && ('L' == 76) && ('M' == 77) \
      && ('N' == 78) && ('O' == 79) && ('P' == 80) && ('Q' == 81) \
      && ('R' == 82) && ('S' == 83) && ('T' == 84) && ('U' == 85) \
      && ('V' == 86) && ('W' == 87) && ('X' == 88) && ('Y' == 89) \
      && ('Z' == 90) && ('[' == 91) && ('\\' == 92) && (']' == 93) \
      && ('^' == 94) && ('_' == 95) && ('a' == 97) && ('b' == 98) \
      && ('c' == 99) && ('d' == 100) && ('e' == 101) && ('f' == 102) \
      && ('g' == 103) && ('h' == 104) && ('i' == 105) && ('j' == 106) \
      && ('k' == 107) && ('l' == 108) && ('m' == 109) && ('n' == 110) \
      && ('o' == 111) && ('p' == 112) && ('q' == 113) && ('r' == 114) \
      && ('s' == 115) && ('t' == 116) && ('u' == 117) && ('v' == 118) \
      && ('w' == 119) && ('x' == 120) && ('y' == 121) && ('z' == 122) \
      && ('{' == 123) && ('|' == 124) && ('}' == 125) && ('~' == 126))
/* The character set is not based on ISO-646.  */
#error "gperf generated tables don't work with this execution character set. Please report a bug to <bug-gperf@gnu.org>."
#endif

#line 1 "frontend/yices/yices_keywords.txt"

#include <string.h>
#include "frontend/yices/yices_lexer.h"
#line 7 "frontend/yices/yices_keywords.txt"
struct keyword_s;

#define TOTAL_KEYWORDS 118
#define MIN_WORD_LENGTH 1
#define MAX_WORD_LENGTH 22
#define MIN_HASH_VALUE 1
#define MAX_HASH_VALUE 340
/* maximum key range = 340, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash (register const char *str, register size_t len)
{
  static const unsigned short asso_values[] =
    {
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341,  80,  80,  75,   0,  90,  17,  10,  60,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
       70,   5,   0,   0, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341,  30,  30, 341,   0, 125,  15,
       10,  10,  60,  65,  30,  50,  75,   5,   5,  10,
       40,  45,  75,  35,   5,   0,   0, 105,  85,  40,
       60,  15,  10, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341, 341, 341, 341,
      341, 341, 341, 341, 341, 341, 341
    };
  register unsigned int hval = len;

  switch (hval)
    {
      default:
        hval += asso_values[(unsigned char)str[4]];
      /*FALLTHROUGH*/
      case 4:
        hval += asso_values[(unsigned char)str[3]];
      /*FALLTHROUGH*/
      case 3:
      case 2:
      case 1:
        hval += asso_values[(unsigned char)str[0]+1];
        break;
    }
  return hval + asso_values[(unsigned char)str[len - 1]];
}

const struct keyword_s *
in_yices_kw (register const char *str, register size_t len)
{
  static const struct keyword_s yices_kw[] =
    {
      {""},
#line 43 "frontend/yices/yices_keywords.txt"
      {">",                      TK_GT},
#line 28 "frontend/yices/yices_keywords.txt"
      {"=>",                     TK_IMPLIES},
      {""}, {""}, {""},
#line 20 "frontend/yices/yices_keywords.txt"
      {"=",                      TK_EQ},
#line 44 "frontend/yices/yices_keywords.txt"
      {">=",                     TK_GE},
#line 27 "frontend/yices/yices_keywords.txt"
      {"<=>",                    TK_IFF},
      {""}, {""},
#line 118 "frontend/yices/yices_keywords.txt"
      {"set-timeout",            TK_SET_TIMEOUT},
#line 42 "frontend/yices/yices_keywords.txt"
      {"<=",                     TK_LE},
#line 98 "frontend/yices/yices_keywords.txt"
      {"let",                    TK_LET},
#line 11 "frontend/yices/yices_keywords.txt"
      {"real",                   TK_REAL},
#line 107 "frontend/yices/yices_keywords.txt"
      {"reset",                  TK_RESET},
#line 13 "frontend/yices/yices_keywords.txt"
      {"scalar",                 TK_SCALAR},
#line 21 "frontend/yices/yices_keywords.txt"
      {"/=",                     TK_DISEQ},
#line 90 "frontend/yices/yices_keywords.txt"
      {"bit",                    TK_BIT},
      {""}, {""},
#line 117 "frontend/yices/yices_keywords.txt"
      {"reset-stats",            TK_RESET_STATS},
      {""},
#line 26 "frontend/yices/yices_keywords.txt"
      {"xor",                    TK_XOR},
#line 92 "frontend/yices/yices_keywords.txt"
      {"ceil",                   TK_CEIL},
#line 73 "frontend/yices/yices_keywords.txt"
      {"bv-lt",                  TK_BV_LT},
#line 77 "frontend/yices/yices_keywords.txt"
      {"bv-slt",                 TK_BV_SLT},
#line 80 "frontend/yices/yices_keywords.txt"
      {"bv-ashr",                TK_BV_ASHR},
#line 39 "frontend/yices/yices_keywords.txt"
      {"/",                      TK_DIV},
#line 9 "frontend/yices/yices_keywords.txt"
      {"bool",                   TK_BOOL},
#line 62 "frontend/yices/yices_keywords.txt"
      {"bv-ashift-right",        TK_BV_ASHIFT_RIGHT},
#line 30 "frontend/yices/yices_keywords.txt"
      {"select",                 TK_SELECT},
#line 79 "frontend/yices/yices_keywords.txt"
      {"bv-lshr",                TK_BV_LSHR},
      {""}, {""}, {""},
#line 76 "frontend/yices/yices_keywords.txt"
      {"bv-sle",                 TK_BV_SLE},
#line 84 "frontend/yices/yices_keywords.txt"
      {"bv-srem",                TK_BV_SREM},
      {""},
#line 67 "frontend/yices/yices_keywords.txt"
      {"bv-repeat",              TK_BV_REPEAT},
#line 102 "frontend/yices/yices_keywords.txt"
      {"check",                  TK_CHECK},
#line 46 "frontend/yices/yices_keywords.txt"
      {"bv-add",                 TK_BV_ADD},
#line 85 "frontend/yices/yices_keywords.txt"
      {"bv-smod",                TK_BV_SMOD},
#line 86 "frontend/yices/yices_keywords.txt"
      {"bv-redor",               TK_BV_REDOR},
      {""},
#line 72 "frontend/yices/yices_keywords.txt"
      {"bv-le",                  TK_BV_LE},
#line 82 "frontend/yices/yices_keywords.txt"
      {"bv-rem",                 TK_BV_REM},
      {""},
#line 25 "frontend/yices/yices_keywords.txt"
      {"not",                    TK_NOT},
#line 87 "frontend/yices/yices_keywords.txt"
      {"bv-redand",              TK_BV_REDAND},
#line 116 "frontend/yices/yices_keywords.txt"
      {"show-stats",             TK_SHOW_STATS},
#line 115 "frontend/yices/yices_keywords.txt"
      {"show-params",            TK_SHOW_PARAMS},
#line 119 "frontend/yices/yices_keywords.txt"
      {"show-timeout",           TK_SHOW_TIMEOUT},
#line 95 "frontend/yices/yices_keywords.txt"
      {"mod",                    TK_MOD},
#line 123 "frontend/yices/yices_keywords.txt"
      {"show-implicant",         TK_SHOW_IMPLICANT},
#line 111 "frontend/yices/yices_keywords.txt"
      {"show-model",             TK_SHOW_MODEL},
#line 78 "frontend/yices/yices_keywords.txt"
      {"bv-shl",                 TK_BV_SHL},
      {""}, {""},
#line 69 "frontend/yices/yices_keywords.txt"
      {"bv-zero-extend",         TK_BV_ZERO_EXTEND},
#line 114 "frontend/yices/yices_keywords.txt"
      {"show-param",             TK_SHOW_PARAM},
#line 40 "frontend/yices/yices_keywords.txt"
      {"^",                      TK_POW},
#line 125 "frontend/yices/yices_keywords.txt"
      {"show-unsat-assumptions", TK_SHOW_UNSAT_ASSUMPTIONS},
#line 126 "frontend/yices/yices_keywords.txt"
      {"show-reduced-model",	TK_SHOW_REDUCED_MODEL},
#line 110 "frontend/yices/yices_keywords.txt"
      {"exit",                   TK_EXIT},
#line 124 "frontend/yices/yices_keywords.txt"
      {"show-unsat-core",        TK_SHOW_UNSAT_CORE},
#line 34 "frontend/yices/yices_keywords.txt"
      {"exists",                 TK_EXISTS},
      {""},
#line 22 "frontend/yices/yices_keywords.txt"
      {"distinct",               TK_DISTINCT},
#line 58 "frontend/yices/yices_keywords.txt"
      {"bv-shift-left0",         TK_BV_SHIFT_LEFT0},
#line 60 "frontend/yices/yices_keywords.txt"
      {"bv-shift-right0",        TK_BV_SHIFT_RIGHT0},
#line 52 "frontend/yices/yices_keywords.txt"
      {"bv-and",                 TK_BV_AND},
#line 55 "frontend/yices/yices_keywords.txt"
      {"bv-nand",                TK_BV_NAND},
      {""},
#line 112 "frontend/yices/yices_keywords.txt"
      {"eval",                   TK_EVAL},
#line 53 "frontend/yices/yices_keywords.txt"
      {"bv-or",                  TK_BV_OR},
#line 41 "frontend/yices/yices_keywords.txt"
      {"<",                      TK_LT},
#line 96 "frontend/yices/yices_keywords.txt"
      {"divides",                TK_DIVIDES},
#line 10 "frontend/yices/yices_keywords.txt"
      {"int",                    TK_INT},
#line 63 "frontend/yices/yices_keywords.txt"
      {"bv-rotate-left",         TK_BV_ROTATE_LEFT},
#line 64 "frontend/yices/yices_keywords.txt"
      {"bv-rotate-right",        TK_BV_ROTATE_RIGHT},
#line 33 "frontend/yices/yices_keywords.txt"
      {"forall",                 TK_FORALL},
#line 23 "frontend/yices/yices_keywords.txt"
      {"or",                     TK_OR},
      {""},
#line 66 "frontend/yices/yices_keywords.txt"
      {"bv-concat",              TK_BV_CONCAT},
#line 71 "frontend/yices/yices_keywords.txt"
      {"bv-gt",                  TK_BV_GT},
#line 75 "frontend/yices/yices_keywords.txt"
      {"bv-sgt",                 TK_BV_SGT},
      {""},
#line 19 "frontend/yices/yices_keywords.txt"
      {"ite",                    TK_ITE},
#line 68 "frontend/yices/yices_keywords.txt"
      {"bv-sign-extend",         TK_BV_SIGN_EXTEND},
#line 17 "frontend/yices/yices_keywords.txt"
      {"false",                  TK_FALSE},
#line 37 "frontend/yices/yices_keywords.txt"
      {"-",                      TK_SUB},
#line 15 "frontend/yices/yices_keywords.txt"
      {"->",                     TK_ARROW},
      {""},
#line 113 "frontend/yices/yices_keywords.txt"
      {"set-param",              TK_SET_PARAM},
#line 65 "frontend/yices/yices_keywords.txt"
      {"bv-extract",             TK_BV_EXTRACT},
#line 74 "frontend/yices/yices_keywords.txt"
      {"bv-sge",                 TK_BV_SGE},
#line 108 "frontend/yices/yices_keywords.txt"
      {"dump-context",           TK_DUMP_CONTEXT},
#line 94 "frontend/yices/yices_keywords.txt"
      {"div",                    TK_IDIV},
#line 105 "frontend/yices/yices_keywords.txt"
      {"push",                   TK_PUSH},
      {""},
#line 32 "frontend/yices/yices_keywords.txt"
      {"update",                 TK_UPDATE},
      {""}, {""}, {""},
#line 70 "frontend/yices/yices_keywords.txt"
      {"bv-ge",                  TK_BV_GE},
#line 51 "frontend/yices/yices_keywords.txt"
      {"bv-not",                 TK_BV_NOT},
      {""}, {""},
#line 103 "frontend/yices/yices_keywords.txt"
      {"check-assuming",         TK_CHECK_ASSUMING},
      {""},
#line 56 "frontend/yices/yices_keywords.txt"
      {"bv-nor",                 TK_BV_NOR},
      {""},
#line 106 "frontend/yices/yices_keywords.txt"
      {"pop",                    TK_POP},
      {""},
#line 89 "frontend/yices/yices_keywords.txt"
      {"bool-to-bv",             TK_BOOL_TO_BV},
#line 100 "frontend/yices/yices_keywords.txt"
      {"define",                 TK_DEFINE},
#line 83 "frontend/yices/yices_keywords.txt"
      {"bv-sdiv",                TK_BV_SDIV},
      {""},
#line 59 "frontend/yices/yices_keywords.txt"
      {"bv-shift-left1",         TK_BV_SHIFT_LEFT1},
#line 61 "frontend/yices/yices_keywords.txt"
      {"bv-shift-right1",        TK_BV_SHIFT_RIGHT1},
#line 99 "frontend/yices/yices_keywords.txt"
      {"define-type",            TK_DEFINE_TYPE},
      {""},
#line 121 "frontend/yices/yices_keywords.txt"
      {"ef-solve",		TK_EF_SOLVE},
#line 12 "frontend/yices/yices_keywords.txt"
      {"bitvector",              TK_BITVECTOR},
#line 91 "frontend/yices/yices_keywords.txt"
      {"floor",                  TK_FLOOR},
#line 122 "frontend/yices/yices_keywords.txt"
      {"export-to-dimacs",       TK_EXPORT_TO_DIMACS},
#line 57 "frontend/yices/yices_keywords.txt"
      {"bv-xnor",                TK_BV_XNOR},
#line 93 "frontend/yices/yices_keywords.txt"
      {"abs",                    TK_ABS},
#line 16 "frontend/yices/yices_keywords.txt"
      {"true",                   TK_TRUE},
      {""},
#line 54 "frontend/yices/yices_keywords.txt"
      {"bv-xor",                 TK_BV_XOR},
      {""}, {""}, {""},
#line 14 "frontend/yices/yices_keywords.txt"
      {"tuple",                  TK_TUPLE},
#line 49 "frontend/yices/yices_keywords.txt"
      {"bv-neg",                 TK_BV_NEG},
#line 18 "frontend/yices/yices_keywords.txt"
      {"if",                     TK_IF},
#line 24 "frontend/yices/yices_keywords.txt"
      {"and",                    TK_AND},
      {""}, {""},
#line 48 "frontend/yices/yices_keywords.txt"
      {"bv-mul",                 TK_BV_MUL},
#line 31 "frontend/yices/yices_keywords.txt"
      {"tuple-update",           TK_UPDATE_TUPLE},
      {""}, {""}, {""},
#line 101 "frontend/yices/yices_keywords.txt"
      {"assert",                 TK_ASSERT},
      {""}, {""}, {""}, {""},
#line 35 "frontend/yices/yices_keywords.txt"
      {"lambda",                 TK_LAMBDA},
      {""}, {""},
#line 104 "frontend/yices/yices_keywords.txt"
      {"echo",                   TK_ECHO},
      {""},
#line 36 "frontend/yices/yices_keywords.txt"
      {"+",                      TK_ADD},
#line 88 "frontend/yices/yices_keywords.txt"
      {"bv-comp",                TK_BV_COMP},
      {""}, {""}, {""},
#line 38 "frontend/yices/yices_keywords.txt"
      {"*",                      TK_MUL},
      {""},
#line 29 "frontend/yices/yices_keywords.txt"
      {"mk-tuple",               TK_MK_TUPLE},
      {""}, {""},
#line 81 "frontend/yices/yices_keywords.txt"
      {"bv-div",                 TK_BV_DIV},
      {""}, {""}, {""}, {""},
#line 97 "frontend/yices/yices_keywords.txt"
      {"is-int",                 TK_IS_INT},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 50 "frontend/yices/yices_keywords.txt"
      {"bv-pow",                 TK_BV_POW},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""},
#line 109 "frontend/yices/yices_keywords.txt"
      {"include",                TK_INCLUDE},
      {""},
#line 120 "frontend/yices/yices_keywords.txt"
      {"help",                   TK_HELP},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""},
#line 47 "frontend/yices/yices_keywords.txt"
      {"bv-sub",                 TK_BV_SUB},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 45 "frontend/yices/yices_keywords.txt"
      {"mk-bv",                  TK_MK_BV}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = yices_kw[key].word;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &yices_kw[key];
        }
    }
  return 0;
}
