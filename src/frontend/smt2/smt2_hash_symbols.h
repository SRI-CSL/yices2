/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -L ANSI-C -W smt2_sym -H hash_sym -E --output-file=frontend/smt2/smt2_hash_symbols.h --lookup-function-name=in_smt2_sym frontend/smt2/smt2_symbols.txt  */
/* Computed positions: -k'1,3-5' */

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

#line 1 "frontend/smt2/smt2_symbols.txt"

#include <string.h>
#include "frontend/smt2/smt2_lexer.h"
#line 7 "frontend/smt2/smt2_symbols.txt"
struct keyword_s;
/* maximum key range = 131, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash_sym (register const char *str, register size_t len)
{
  static const unsigned char asso_values[] =
    {
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132,  42,   2, 132, 125,  70,   0, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
       80,  45,  35, 132, 132,  10,   0, 132, 132, 132,
       80, 132, 132,  30, 132, 132, 132, 132, 132, 132,
      132, 132,   5, 132, 132, 132, 100, 132, 132, 132,
      132, 132, 132, 132, 132,  20, 132,   0,   0,  10,
       10,   0,  10,  35,  45,  20, 132, 132,  45,  40,
        0,   0,  10, 132,   0,  25,   5,   5,  20, 132,
       95,   5,  75, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132, 132, 132, 132, 132,
      132, 132, 132, 132, 132, 132
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
        hval += asso_values[(unsigned char)str[2]];
      /*FALLTHROUGH*/
      case 2:
      case 1:
        hval += asso_values[(unsigned char)str[0]];
        break;
    }
  return hval;
}

const struct keyword_s *
in_smt2_sym (register const char *str, register size_t len)
{
  enum
    {
      TOTAL_KEYWORDS = 72,
      MIN_WORD_LENGTH = 1,
      MAX_WORD_LENGTH = 12,
      MIN_HASH_VALUE = 1,
      MAX_HASH_VALUE = 131
    };

  static const struct keyword_s smt2_sym[] =
    {
      {""},
#line 28 "frontend/smt2/smt2_symbols.txt"
      {"/",                            SMT2_SYM_DIVIDES},
#line 15 "frontend/smt2/smt2_symbols.txt"
      {"or",                           SMT2_SYM_OR},
#line 26 "frontend/smt2/smt2_symbols.txt"
      {"+",                            SMT2_SYM_PLUS},
#line 49 "frontend/smt2/smt2_symbols.txt"
      {"bvor",                         SMT2_SYM_BVOR},
#line 51 "frontend/smt2/smt2_symbols.txt"
      {"bvnor",                        SMT2_SYM_BVNOR},
#line 50 "frontend/smt2/smt2_symbols.txt"
      {"bvnand",                       SMT2_SYM_BVNAND},
      {""},
#line 12 "frontend/smt2/smt2_symbols.txt"
      {"not",                          SMT2_SYM_NOT},
      {""},
#line 47 "frontend/smt2/smt2_symbols.txt"
      {"bvnot",                        SMT2_SYM_BVNOT},
#line 59 "frontend/smt2/smt2_symbols.txt"
      {"bvurem",                       SMT2_SYM_BVUREM},
#line 42 "frontend/smt2/smt2_symbols.txt"
      {"extract",                      SMT2_SYM_EXTRACT},
#line 14 "frontend/smt2/smt2_symbols.txt"
      {"and",                          SMT2_SYM_AND},
#line 10 "frontend/smt2/smt2_symbols.txt"
      {"true",                         SMT2_SYM_TRUE},
#line 48 "frontend/smt2/smt2_symbols.txt"
      {"bvand",                        SMT2_SYM_BVAND},
#line 43 "frontend/smt2/smt2_symbols.txt"
      {"repeat",                       SMT2_SYM_REPEAT},
#line 46 "frontend/smt2/smt2_symbols.txt"
      {"bvredor",                      SMT2_SYM_BVREDOR},
#line 45 "frontend/smt2/smt2_symbols.txt"
      {"bvredand",                     SMT2_SYM_BVREDAND},
      {""},
#line 20 "frontend/smt2/smt2_symbols.txt"
      {"Array",                        SMT2_SYM_ARRAY},
#line 68 "frontend/smt2/smt2_symbols.txt"
      {"rotate_left",                  SMT2_SYM_ROTATE_LEFT},
#line 69 "frontend/smt2/smt2_symbols.txt"
      {"rotate_right",                 SMT2_SYM_ROTATE_RIGHT},
#line 19 "frontend/smt2/smt2_symbols.txt"
      {"ite",                          SMT2_SYM_ITE},
      {""},
#line 55 "frontend/smt2/smt2_symbols.txt"
      {"bvadd",                        SMT2_SYM_BVADD},
#line 41 "frontend/smt2/smt2_symbols.txt"
      {"concat",                       SMT2_SYM_CONCAT},
      {""},
#line 35 "frontend/smt2/smt2_symbols.txt"
      {"abs",                          SMT2_SYM_ABS},
      {""},
#line 22 "frontend/smt2/smt2_symbols.txt"
      {"store",                        SMT2_SYM_STORE},
#line 61 "frontend/smt2/smt2_symbols.txt"
      {"bvsrem",                       SMT2_SYM_BVSREM},
#line 36 "frontend/smt2/smt2_symbols.txt"
      {"to_real",                      SMT2_SYM_TO_REAL},
#line 33 "frontend/smt2/smt2_symbols.txt"
      {"div",                          SMT2_SYM_DIV},
      {""},
#line 56 "frontend/smt2/smt2_symbols.txt"
      {"bvsub",                        SMT2_SYM_BVSUB},
#line 32 "frontend/smt2/smt2_symbols.txt"
      {">",                            SMT2_SYM_GT},
#line 31 "frontend/smt2/smt2_symbols.txt"
      {">=",                           SMT2_SYM_GE},
#line 23 "frontend/smt2/smt2_symbols.txt"
      {"Int",                          SMT2_SYM_INT},
      {""},
#line 54 "frontend/smt2/smt2_symbols.txt"
      {"bvneg",                        SMT2_SYM_BVNEG},
#line 58 "frontend/smt2/smt2_symbols.txt"
      {"bvudiv",                       SMT2_SYM_BVUDIV},
      {""},
#line 27 "frontend/smt2/smt2_symbols.txt"
      {"*",                            SMT2_SYM_TIMES},
      {""},
#line 73 "frontend/smt2/smt2_symbols.txt"
      {"bvuge",                        SMT2_SYM_BVUGE},
#line 17 "frontend/smt2/smt2_symbols.txt"
      {"=",                            SMT2_SYM_EQ},
#line 13 "frontend/smt2/smt2_symbols.txt"
      {"=>",                           SMT2_SYM_IMPLIES},
      {""},
#line 9 "frontend/smt2/smt2_symbols.txt"
      {"Bool",                         SMT2_SYM_BOOL},
#line 72 "frontend/smt2/smt2_symbols.txt"
      {"bvugt",                        SMT2_SYM_BVUGT},
#line 37 "frontend/smt2/smt2_symbols.txt"
      {"to_int",                       SMT2_SYM_TO_INT},
      {""},
#line 34 "frontend/smt2/smt2_symbols.txt"
      {"mod",                          SMT2_SYM_MOD},
#line 24 "frontend/smt2/smt2_symbols.txt"
      {"Real",                         SMT2_SYM_REAL},
#line 71 "frontend/smt2/smt2_symbols.txt"
      {"bvule",                        SMT2_SYM_BVULE},
#line 44 "frontend/smt2/smt2_symbols.txt"
      {"bvcomp",                       SMT2_SYM_BVCOMP},
      {""}, {""}, {""},
#line 70 "frontend/smt2/smt2_symbols.txt"
      {"bvult",                        SMT2_SYM_BVULT},
#line 60 "frontend/smt2/smt2_symbols.txt"
      {"bvsdiv",                       SMT2_SYM_BVSDIV},
      {""}, {""}, {""},
#line 77 "frontend/smt2/smt2_symbols.txt"
      {"bvsge",                        SMT2_SYM_BVSGE},
#line 38 "frontend/smt2/smt2_symbols.txt"
      {"is_int",                       SMT2_SYM_IS_INT},
      {""},
#line 18 "frontend/smt2/smt2_symbols.txt"
      {"distinct",                     SMT2_SYM_DISTINCT},
      {""},
#line 76 "frontend/smt2/smt2_symbols.txt"
      {"bvsgt",                        SMT2_SYM_BVSGT},
#line 62 "frontend/smt2/smt2_symbols.txt"
      {"bvsmod",                       SMT2_SYM_BVSMOD},
      {""}, {""}, {""},
#line 75 "frontend/smt2/smt2_symbols.txt"
      {"bvsle",                        SMT2_SYM_BVSLE},
#line 65 "frontend/smt2/smt2_symbols.txt"
      {"bvashr",                       SMT2_SYM_BVASHR},
      {""}, {""}, {""},
#line 74 "frontend/smt2/smt2_symbols.txt"
      {"bvslt",                        SMT2_SYM_BVSLT},
#line 30 "frontend/smt2/smt2_symbols.txt"
      {"<",                            SMT2_SYM_LT},
#line 29 "frontend/smt2/smt2_symbols.txt"
      {"<=",                           SMT2_SYM_LE},
      {""},
#line 39 "frontend/smt2/smt2_symbols.txt"
      {"divisible",                    SMT2_SYM_DIVISIBLE},
#line 11 "frontend/smt2/smt2_symbols.txt"
      {"false",                        SMT2_SYM_FALSE},
#line 21 "frontend/smt2/smt2_symbols.txt"
      {"select",                       SMT2_SYM_SELECT},
      {""}, {""}, {""}, {""},
#line 67 "frontend/smt2/smt2_symbols.txt"
      {"sign_extend",                  SMT2_SYM_SIGN_EXTEND},
      {""}, {""}, {""},
#line 57 "frontend/smt2/smt2_symbols.txt"
      {"bvmul",                        SMT2_SYM_BVMUL},
#line 79 "frontend/smt2/smt2_symbols.txt"
      {"ff.add",                       SMT2_SYM_FFADD},
      {""},
#line 16 "frontend/smt2/smt2_symbols.txt"
      {"xor",                          SMT2_SYM_XOR},
      {""},
#line 52 "frontend/smt2/smt2_symbols.txt"
      {"bvxor",                        SMT2_SYM_BVXOR},
#line 53 "frontend/smt2/smt2_symbols.txt"
      {"bvxnor",                       SMT2_SYM_BVXNOR},
      {""}, {""}, {""}, {""},
#line 66 "frontend/smt2/smt2_symbols.txt"
      {"zero_extend",                  SMT2_SYM_ZERO_EXTEND},
      {""}, {""}, {""}, {""},
#line 40 "frontend/smt2/smt2_symbols.txt"
      {"BitVec",                       SMT2_SYM_BITVEC},
      {""}, {""}, {""}, {""},
#line 78 "frontend/smt2/smt2_symbols.txt"
      {"FiniteField",                  SMT2_SYM_FINITEFIELD},
      {""}, {""}, {""},
#line 63 "frontend/smt2/smt2_symbols.txt"
      {"bvshl",                        SMT2_SYM_BVSHL},
#line 64 "frontend/smt2/smt2_symbols.txt"
      {"bvlshr",                       SMT2_SYM_BVLSHR},
      {""}, {""}, {""}, {""},
#line 25 "frontend/smt2/smt2_symbols.txt"
      {"-",                            SMT2_SYM_MINUS},
      {""}, {""}, {""}, {""},
#line 80 "frontend/smt2/smt2_symbols.txt"
      {"ff.mul",                       SMT2_SYM_FFMUL}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash_sym (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = smt2_sym[key].word;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &smt2_sym[key];
        }
    }
  return 0;
}
