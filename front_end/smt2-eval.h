#ifndef _SMT2_EVAL_H_
#define _SMT2_EVAL_H_
#include "vector.h"

enum value_tag_t { vtUNKNOWN, vtTERM, vtSORT, vtSYMBOL, vtSTRING,
		   vtEXTRACT, vtSIGN_EXTEND, vtREPEAT, vtROTATE_LEFT,
		   vtROTATE_RIGHT, vtZERO_EXTEND };

typedef struct {
    enum value_tag_t	tag;
    union {
	term_t		term;
	type_t		sort;
	const char	*str;
	struct {
	    int		i0, i1;
	}		fn;
    }			v;
} value_t;

static inline value_t UNKNOWNval() {
    value_t rv;
    rv.tag = vtUNKNOWN;
    return rv; }
static inline value_t TERMval(term_t t) {
    value_t rv;
    rv.tag = vtTERM;
    rv.v.term = t;
    return rv; }
static inline value_t SORTval(type_t t) {
    value_t rv;
    rv.tag = vtSORT;
    rv.v.sort = t;
    return rv; }
static inline value_t SYMBOLval(const char *v) {
    value_t rv;
    rv.tag = vtSYMBOL;
    rv.v.str = v;
    return rv; }
static inline value_t STRINGval(const char *v) {
    value_t rv;
    rv.tag = vtSTRING;
    rv.v.str = v;
    return rv; }
static inline value_t FNval(enum value_tag_t fn, int i0, int i1) {
    value_t rv;
    rv.tag = fn;
    rv.v.fn.i0 = i0;
    rv.v.fn.i1 = i1;
    return rv; }

void eval_init();
void print_value(FILE *, value_t val);
value_t eval_sexpr(value_t fn, int ac, value_t *av);
type_t indexed_type(const char *sym, int idxcnt, int *idx);
value_t indexed_value(const char *sym, int idxcnt, int *idx);
#endif /* _SMT2_EVAL_H_ */
