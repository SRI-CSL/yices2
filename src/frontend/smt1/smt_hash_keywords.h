/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -L ANSI-C -W smt_kw --output-file=frontend/smt1/smt_hash_keywords.h --lookup-function-name=in_smt_kw frontend/smt1/smt_keywords.txt  */
/* Computed positions: -k'1,3-4,7,$' */

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

#line 1 "frontend/smt1/smt_keywords.txt"

#include <string.h>
#include "frontend/smt1/smt_lexer.h"
#line 7 "frontend/smt1/smt_keywords.txt"
struct keyword_s;

#define TOTAL_KEYWORDS 96
#define MIN_WORD_LENGTH 1
#define MAX_WORD_LENGTH 12
#define MIN_HASH_VALUE 1
#define MAX_HASH_VALUE 211
/* maximum key range = 211, duplicates = 0 */

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
  static const unsigned char asso_values[] =
    {
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 105, 100, 212,  95, 212,  90,  15,   5,
       50, 212, 212, 212, 212, 212, 212, 212,   0, 212,
       50,  10,   0, 212, 212,  50,  55, 212, 212, 212,
      212, 212, 212,   5, 212, 212, 212, 212, 212, 212,
      212, 212,   0, 212, 212, 212,  55, 212, 212, 212,
      212, 212, 212, 212, 212,  30, 212,  45,   0,  40,
       15,   5,  95,  35,  50,   0, 212,   0,  15,  17,
       20,  70,  15, 100,  10,   0,   0,  10,  50, 212,
       30,   0,  10, 212, 212, 212,  25, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212, 212, 212, 212, 212,
      212, 212, 212, 212, 212, 212
    };
  register unsigned int hval = len;

  switch (hval)
    {
      default:
        hval += asso_values[(unsigned char)str[6]];
      /*FALLTHROUGH*/
      case 6:
      case 5:
      case 4:
        hval += asso_values[(unsigned char)str[3]];
      /*FALLTHROUGH*/
      case 3:
        hval += asso_values[(unsigned char)str[2]];
      /*FALLTHROUGH*/
      case 2:
      case 1:
        hval += asso_values[(unsigned char)str[0]];
        break;
    }
  return hval + asso_values[(unsigned char)str[len - 1]];
}

const struct keyword_s *
in_smt_kw (register const char *str, register size_t len)
{
  static const struct keyword_s smt_kw[] =
    {
      {""},
#line 26 "frontend/smt1/smt_keywords.txt"
      {">",              SMT_TK_GT},
      {""},
#line 91 "frontend/smt1/smt_keywords.txt"
      {"sat",            SMT_TK_SAT},
      {""}, {""}, {""}, {""},
#line 32 "frontend/smt1/smt_keywords.txt"
      {"Int",            SMT_TK_INT},
      {""}, {""},
#line 76 "frontend/smt1/smt_keywords.txt"
      {"exists",         SMT_TK_EXISTS},
#line 27 "frontend/smt1/smt_keywords.txt"
      {">=",             SMT_TK_GE},
#line 84 "frontend/smt1/smt_keywords.txt"
      {"ite",            SMT_TK_ITE},
#line 37 "frontend/smt1/smt_keywords.txt"
      {"bit1",           SMT_TK_BIT1},
#line 65 "frontend/smt1/smt_keywords.txt"
      {"bvsub",          SMT_TK_BVSUB},
      {""}, {""},
#line 85 "frontend/smt1/smt_keywords.txt"
      {"let",            SMT_TK_LET},
#line 46 "frontend/smt1/smt_keywords.txt"
      {"bvlt",           SMT_TK_BVLT},
#line 62 "frontend/smt1/smt_keywords.txt"
      {"bvslt",          SMT_TK_BVSLT},
#line 25 "frontend/smt1/smt_keywords.txt"
      {"=",              SMT_TK_EQ},
#line 77 "frontend/smt1/smt_keywords.txt"
      {"extract",        SMT_TK_EXTRACT},
#line 86 "frontend/smt1/smt_keywords.txt"
      {"not",            SMT_TK_NOT},
#line 99 "frontend/smt1/smt_keywords.txt"
      {"true",           SMT_TK_TRUE},
#line 60 "frontend/smt1/smt_keywords.txt"
      {"bvsle",          SMT_TK_BVSLE},
#line 92 "frontend/smt1/smt_keywords.txt"
      {"select",         SMT_TK_SELECT},
      {""}, {""}, {""},
#line 70 "frontend/smt1/smt_keywords.txt"
      {"bvult",          SMT_TK_BVULT},
#line 45 "frontend/smt1/smt_keywords.txt"
      {"bvlshr",         SMT_TK_BVLSHR},
      {""},
#line 64 "frontend/smt1/smt_keywords.txt"
      {"bvsrem",         SMT_TK_BVSREM},
#line 36 "frontend/smt1/smt_keywords.txt"
      {"bit0",           SMT_TK_BIT0},
#line 69 "frontend/smt1/smt_keywords.txt"
      {"bvule",          SMT_TK_BVULE},
#line 88 "frontend/smt1/smt_keywords.txt"
      {"repeat",         SMT_TK_REPEAT},
#line 83 "frontend/smt1/smt_keywords.txt"
      {"implies",        SMT_TK_IMPLIES},
#line 63 "frontend/smt1/smt_keywords.txt"
      {"bvsmod",         SMT_TK_BVSMOD},
#line 43 "frontend/smt1/smt_keywords.txt"
      {"bvgt",           SMT_TK_BVGT},
#line 58 "frontend/smt1/smt_keywords.txt"
      {"bvsgt",          SMT_TK_BVSGT},
#line 16 "frontend/smt1/smt_keywords.txt"
      {":extrasorts",    SMT_TK_EXTRASORTS},
#line 54 "frontend/smt1/smt_keywords.txt"
      {"bvredor",        SMT_TK_BVREDOR},
#line 71 "frontend/smt1/smt_keywords.txt"
      {"bvurem",         SMT_TK_BVUREM},
      {""},
#line 56 "frontend/smt1/smt_keywords.txt"
      {"bvsge",          SMT_TK_BVSGE},
#line 13 "frontend/smt1/smt_keywords.txt"
      {":assumption",    SMT_TK_ASSUMPTION},
#line 47 "frontend/smt1/smt_keywords.txt"
      {"bvmul",          SMT_TK_BVMUL},
      {""},
#line 21 "frontend/smt1/smt_keywords.txt"
      {":pat",           SMT_TK_PAT},
#line 68 "frontend/smt1/smt_keywords.txt"
      {"bvugt",          SMT_TK_BVUGT},
#line 104 "frontend/smt1/smt_keywords.txt"
      {"~",              SMT_TK_TILDE},
#line 22 "frontend/smt1/smt_keywords.txt"
      {":status",        SMT_TK_STATUS},
#line 102 "frontend/smt1/smt_keywords.txt"
      {"xor",            SMT_TK_XOR},
      {""},
#line 67 "frontend/smt1/smt_keywords.txt"
      {"bvuge",          SMT_TK_BVUGE},
#line 15 "frontend/smt1/smt_keywords.txt"
      {":extrapreds",    SMT_TK_EXTRAPREDS},
      {""},
#line 53 "frontend/smt1/smt_keywords.txt"
      {"bvredand",       SMT_TK_BVREDAND},
      {""},
#line 101 "frontend/smt1/smt_keywords.txt"
      {"unsat",          SMT_TK_UNSAT},
#line 40 "frontend/smt1/smt_keywords.txt"
      {"bvashr",         SMT_TK_BVASHR},
#line 24 "frontend/smt1/smt_keywords.txt"
      {"<=",             SMT_TK_LE},
#line 75 "frontend/smt1/smt_keywords.txt"
      {"distinct",       SMT_TK_DISTINCT},
      {""},
#line 49 "frontend/smt1/smt_keywords.txt"
      {"bvneg",          SMT_TK_BVNEG},
#line 72 "frontend/smt1/smt_keywords.txt"
      {"bvxnor",         SMT_TK_BVXNOR},
#line 81 "frontend/smt1/smt_keywords.txt"
      {"if_then_else",   SMT_TK_IF_THEN_ELSE},
      {""}, {""},
#line 59 "frontend/smt1/smt_keywords.txt"
      {"bvshl",          SMT_TK_BVSHL},
#line 55 "frontend/smt1/smt_keywords.txt"
      {"bvsdiv",         SMT_TK_BVSDIV},
      {""}, {""}, {""}, {""},
#line 20 "frontend/smt1/smt_keywords.txt"
      {":notes",         SMT_TK_NOTES},
#line 100 "frontend/smt1/smt_keywords.txt"
      {"unknown",        SMT_TK_UNKNOWN},
#line 34 "frontend/smt1/smt_keywords.txt"
      {"and",            SMT_TK_AND},
#line 33 "frontend/smt1/smt_keywords.txt"
      {"Real",           SMT_TK_REAL},
#line 38 "frontend/smt1/smt_keywords.txt"
      {"bvadd",          SMT_TK_BVADD},
#line 66 "frontend/smt1/smt_keywords.txt"
      {"bvudiv",         SMT_TK_BVUDIV},
#line 87 "frontend/smt1/smt_keywords.txt"
      {"or",             SMT_TK_OR},
      {""}, {""},
#line 39 "frontend/smt1/smt_keywords.txt"
      {"bvand",          SMT_TK_BVAND},
#line 48 "frontend/smt1/smt_keywords.txt"
      {"bvnand",         SMT_TK_BVNAND},
      {""}, {""}, {""},
#line 98 "frontend/smt1/smt_keywords.txt"
      {"store",          SMT_TK_STORE},
#line 19 "frontend/smt1/smt_keywords.txt"
      {":nopat",         SMT_TK_NOPAT},
      {""}, {""},
#line 52 "frontend/smt1/smt_keywords.txt"
      {"bvor",           SMT_TK_BVOR},
#line 51 "frontend/smt1/smt_keywords.txt"
      {"bvnot",          SMT_TK_BVNOT},
#line 89 "frontend/smt1/smt_keywords.txt"
      {"rotate_left",    SMT_TK_ROTATE_LEFT},
#line 90 "frontend/smt1/smt_keywords.txt"
      {"rotate_right",   SMT_TK_ROTATE_RIGHT},
      {""}, {""}, {""},
#line 23 "frontend/smt1/smt_keywords.txt"
      {"<",              SMT_TK_LT},
      {""}, {""},
#line 79 "frontend/smt1/smt_keywords.txt"
      {"flet",           SMT_TK_FLET},
#line 50 "frontend/smt1/smt_keywords.txt"
      {"bvnor",          SMT_TK_BVNOR},
#line 74 "frontend/smt1/smt_keywords.txt"
      {"concat",         SMT_TK_CONCAT},
      {""}, {""}, {""},
#line 28 "frontend/smt1/smt_keywords.txt"
      {"Array",          SMT_TK_ARRAY},
#line 97 "frontend/smt1/smt_keywords.txt"
      {"sign_extend",    SMT_TK_SIGN_EXTEND},
      {""}, {""},
#line 35 "frontend/smt1/smt_keywords.txt"
      {"benchmark",      SMT_TK_BENCHMARK},
#line 73 "frontend/smt1/smt_keywords.txt"
      {"bvxor",          SMT_TK_BVXOR},
#line 29 "frontend/smt1/smt_keywords.txt"
      {"Array1",         SMT_TK_ARRAY1},
      {""}, {""}, {""},
#line 78 "frontend/smt1/smt_keywords.txt"
      {"false",          SMT_TK_FALSE},
#line 61 "frontend/smt1/smt_keywords.txt"
      {"bvsleq",         SMT_TK_BVSLEQ},
#line 96 "frontend/smt1/smt_keywords.txt"
      {"shift_right1",   SMT_TK_SHIFT_RIGHT1},
      {""}, {""},
#line 44 "frontend/smt1/smt_keywords.txt"
      {"bvleq",          SMT_TK_BVLEQ},
#line 94 "frontend/smt1/smt_keywords.txt"
      {"shift_left1",    SMT_TK_SHIFT_LEFT1},
      {""}, {""}, {""}, {""},
#line 41 "frontend/smt1/smt_keywords.txt"
      {"bvcomp",         SMT_TK_BVCOMP},
#line 95 "frontend/smt1/smt_keywords.txt"
      {"shift_right0",   SMT_TK_SHIFT_RIGHT0},
      {""}, {""},
#line 14 "frontend/smt1/smt_keywords.txt"
      {":extrafuns",     SMT_TK_EXTRAFUNS},
#line 93 "frontend/smt1/smt_keywords.txt"
      {"shift_left0",    SMT_TK_SHIFT_LEFT0},
      {""}, {""}, {""}, {""},
#line 57 "frontend/smt1/smt_keywords.txt"
      {"bvsgeq",         SMT_TK_BVSGEQ},
      {""}, {""}, {""},
#line 42 "frontend/smt1/smt_keywords.txt"
      {"bvgeq",          SMT_TK_BVGEQ},
#line 103 "frontend/smt1/smt_keywords.txt"
      {"zero_extend",    SMT_TK_ZERO_EXTEND},
      {""},
#line 17 "frontend/smt1/smt_keywords.txt"
      {":formula",       SMT_TK_FORMULA},
      {""}, {""},
#line 18 "frontend/smt1/smt_keywords.txt"
      {":logic",         SMT_TK_LOGIC},
      {""}, {""}, {""}, {""},
#line 31 "frontend/smt1/smt_keywords.txt"
      {"BitVec",         SMT_TK_BITVEC},
      {""}, {""}, {""}, {""},
#line 30 "frontend/smt1/smt_keywords.txt"
      {"Array2",         SMT_TK_ARRAY2},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 80 "frontend/smt1/smt_keywords.txt"
      {"forall",         SMT_TK_FORALL},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 12 "frontend/smt1/smt_keywords.txt"
      {"/",              SMT_TK_DIV},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 11 "frontend/smt1/smt_keywords.txt"
      {"-",              SMT_TK_SUB},
      {""},
#line 82 "frontend/smt1/smt_keywords.txt"
      {"iff",            SMT_TK_IFF},
      {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 10 "frontend/smt1/smt_keywords.txt"
      {"+",              SMT_TK_ADD},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
#line 9 "frontend/smt1/smt_keywords.txt"
      {"*",              SMT_TK_MUL}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = smt_kw[key].word;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &smt_kw[key];
        }
    }
  return 0;
}
