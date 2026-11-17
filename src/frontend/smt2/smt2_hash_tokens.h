/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -C -L ANSI-C -W smt2_tk -H hash_tk -E --output-file=frontend/smt2/smt2_hash_tokens.h --lookup-function-name=in_smt2_tk frontend/smt2/smt2_tokens.txt  */
/* Computed positions: -k'1,3,$' */

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

#line 1 "frontend/smt2/smt2_tokens.txt"

#include <string.h>
#include "frontend/smt2/smt2_lexer.h"
#line 7 "frontend/smt2/smt2_tokens.txt"
struct keyword_s;
/* maximum key range = 84, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash_tk (register const char *str, register size_t len)
{
  static const unsigned char asso_values[] =
    {
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 15, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 10,  5, 85,
      85,  0, 85, 85, 85, 85,  0,  0,  0, 85,
      85, 85,  0,  0, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85,  0, 85, 10, 85,  0,
       0, 15, 25, 15, 50, 40, 85, 85, 30, 85,
       0, 15,  5, 85,  0,  5,  0, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85, 85, 85, 85, 85,
      85, 85, 85, 85, 85, 85
    };
  register unsigned int hval = len;

  switch (hval)
    {
      default:
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
in_smt2_tk (register const char *str, register size_t len)
{
  enum
    {
      TOTAL_KEYWORDS = 39,
      MIN_WORD_LENGTH = 1,
      MAX_WORD_LENGTH = 27,
      MIN_HASH_VALUE = 1,
      MAX_HASH_VALUE = 84
    };

  static const struct keyword_s smt2_tk[] =
    {
      {""},
#line 13 "frontend/smt2/smt2_tokens.txt"
      {"_",                            SMT2_TK_UNDERSCORE},
      {""}, {""}, {""}, {""},
#line 12 "frontend/smt2/smt2_tokens.txt"
      {"STRING",                       SMT2_TK_STR,},
#line 10 "frontend/smt2/smt2_tokens.txt"
      {"NUMERAL",                      SMT2_TK_NUM},
#line 9 "frontend/smt2/smt2_tokens.txt"
      {"par",                          SMT2_TK_PAR},
      {""},
#line 46 "frontend/smt2/smt2_tokens.txt"
      {"reset",                        SMT2_TK_RESET},
#line 25 "frontend/smt2/smt2_tokens.txt"
      {"declare-fun",                  SMT2_TK_DECLARE_FUN},
#line 23 "frontend/smt2/smt2_tokens.txt"
      {"declare-sort",                 SMT2_TK_DECLARE_SORT},
#line 24 "frontend/smt2/smt2_tokens.txt"
      {"declare-const",                SMT2_TK_DECLARE_CONST},
#line 42 "frontend/smt2/smt2_tokens.txt"
      {"set-logic",                    SMT2_TK_SET_LOGIC},
#line 44 "frontend/smt2/smt2_tokens.txt"
      {"set-option",                   SMT2_TK_SET_OPTION},
      {""},
#line 15 "frontend/smt2/smt2_tokens.txt"
      {"as",                           SMT2_TK_AS},
#line 40 "frontend/smt2/smt2_tokens.txt"
      {"pop",                          SMT2_TK_POP},
      {""}, {""},
#line 19 "frontend/smt2/smt2_tokens.txt"
      {"assert",                       SMT2_TK_ASSERT},
#line 11 "frontend/smt2/smt2_tokens.txt"
      {"DECIMAL",                      SMT2_TK_DEC},
      {""},
#line 20 "frontend/smt2/smt2_tokens.txt"
      {"check-sat",                    SMT2_TK_CHECK_SAT},
#line 34 "frontend/smt2/smt2_tokens.txt"
      {"get-option",                   SMT2_TK_GET_OPTION},
#line 47 "frontend/smt2/smt2_tokens.txt"
      {"reset-assertions",             SMT2_TK_RESET_ASSERTIONS},
      {""},
#line 43 "frontend/smt2/smt2_tokens.txt"
      {"set-info",                     SMT2_TK_SET_INFO},
#line 31 "frontend/smt2/smt2_tokens.txt"
      {"get-assignment",               SMT2_TK_GET_ASSIGNMENT},
      {""},
#line 14 "frontend/smt2/smt2_tokens.txt"
      {"!",                            SMT2_TK_BANG},
      {""},
#line 16 "frontend/smt2/smt2_tokens.txt"
      {"let",                          SMT2_TK_LET},
#line 30 "frontend/smt2/smt2_tokens.txt"
      {"get-assertions",               SMT2_TK_GET_ASSERTIONS},
#line 28 "frontend/smt2/smt2_tokens.txt"
      {"define-fun",                   SMT2_TK_DEFINE_FUN},
#line 26 "frontend/smt2/smt2_tokens.txt"
      {"define-sort",                  SMT2_TK_DEFINE_SORT},
#line 27 "frontend/smt2/smt2_tokens.txt"
      {"define-const",                 SMT2_TK_DEFINE_CONST},
#line 32 "frontend/smt2/smt2_tokens.txt"
      {"get-info",                     SMT2_TK_GET_INFO},
#line 39 "frontend/smt2/smt2_tokens.txt"
      {"get-value",                    SMT2_TK_GET_VALUE},
      {""},
#line 36 "frontend/smt2/smt2_tokens.txt"
      {"get-unsat-assumptions",        SMT2_TK_GET_UNSAT_ASSUMPTIONS},
#line 38 "frontend/smt2/smt2_tokens.txt"
      {"get-unsat-model-interpolant",  SMT2_TK_GET_UNSAT_MODEL_INTERPOLANT},
      {""},
#line 37 "frontend/smt2/smt2_tokens.txt"
      {"get-unsat-core",               SMT2_TK_GET_UNSAT_CORE},
      {""}, {""}, {""},
#line 21 "frontend/smt2/smt2_tokens.txt"
      {"check-sat-assuming",           SMT2_TK_CHECK_SAT_ASSUMING},
#line 35 "frontend/smt2/smt2_tokens.txt"
      {"get-proof",                    SMT2_TK_GET_PROOF},
      {""}, {""}, {""}, {""},
#line 33 "frontend/smt2/smt2_tokens.txt"
      {"get-model",                    SMT2_TK_GET_MODEL},
      {""}, {""}, {""}, {""},
#line 29 "frontend/smt2/smt2_tokens.txt"
      {"exit",                         SMT2_TK_EXIT},
      {""},
#line 18 "frontend/smt2/smt2_tokens.txt"
      {"forall",                       SMT2_TK_FORALL},
      {""}, {""},
#line 41 "frontend/smt2/smt2_tokens.txt"
      {"push",                         SMT2_TK_PUSH},
      {""},
#line 17 "frontend/smt2/smt2_tokens.txt"
      {"exists",                       SMT2_TK_EXISTS},
      {""}, {""},
#line 22 "frontend/smt2/smt2_tokens.txt"
      {"check-sat-assuming-model",     SMT2_TK_CHECK_SAT_ASSUMING_MODEL},
      {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""}, {""},
      {""}, {""}, {""}, {""}, {""},
#line 45 "frontend/smt2/smt2_tokens.txt"
      {"echo",                         SMT2_TK_ECHO}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash_tk (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = smt2_tk[key].word;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &smt2_tk[key];
        }
    }
  return 0;
}
