#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include "gmp.h"
#include "yices.h"
#include "smt2-eval.h"
#include "hash.h"


extern void yyerror(const char *, ...);
extern int lineno;

static hash_table *symbolfunc = 0;
const char *cached_string(const char *p);

/* eval functions -- wrappers that reorder the terms as appropriate and
 * call a yices term function */
/* General functions */
static term_t eval_unary(int ac, term_t *av, void *fn_) {
    term_t (*fn)(term_t) = fn_;
    assert(ac == 1);
    return fn(av[0]); }

static term_t eval_binary(int ac, term_t *av, void *fn_) {
    term_t (*fn)(term_t, term_t) = fn_;
    assert(ac == 2);
    return fn(av[0], av[1]); }

static term_t eval_binary_left_assoc(int ac, term_t *av, void *fn_) {
    term_t (*fn)(term_t, term_t) = fn_;
    int i;
    assert (ac >= 2);
    for (i = 1; i < ac; i++)
	av[0] = fn(av[0], av[i]);
    return av[0]; }

static term_t eval_binary_right_assoc(int ac, term_t *av, void *fn_) {
    term_t (*fn)(term_t, term_t) = fn_;
    int i;
    assert (ac >= 2);
    for (i = ac-2; i > 0; i--)
	av[i] = fn(av[i], av[i+1]);
    return fn(av[0], av[1]); }

static term_t eval_binary_left_and(int ac, term_t *av, void *fn_) {
    term_t (*fn)(term_t, term_t) = fn_;
    int i;
    assert (ac >= 2);
    for (i = 0; i < ac-1; i++)
	av[i] = fn(av[i], av[i+1]);
    if (ac > 2)
	return yices_and(ac-1, av);
    else
	return av[0]; }

static term_t eval_trinary(int ac, term_t *av, void *fn_) {
    term_t (*fn)(term_t, term_t, term_t) = fn_;
    assert(ac == 3);
    return fn(av[0], av[1], av[2]); }

static term_t eval_nary(int ac, term_t *av, void *fn_) {
    term_t (*fn)(uint32_t, term_t *) = fn_;
    return fn(ac, av); }

/* Core theory functions */
/* Ints theory functions */
static term_t eval_minus(int ac, term_t *av, void *ign) {
    if (ac == 1)
	return yices_neg(av[0]);
    assert(ac == 2);
    return yices_sub(av[0], av[1]); }

/* Reals theory functions */
/* Reals_Ints theory functions */
/* ArraysEx theory functions */
static term_t eval_select(int ac, term_t *av, void *ign) {
    assert(ac == 2);
    return yices_application(av[0], 1, av+1);
}
static term_t eval_store(int ac, term_t *av, void *ign) {
    assert(ac == 3);
    return yices_update(av[0], 1, av+1, av[2]);
}

/* Fixed_Size_BitVectors theory functions */

struct fn_info {
    const char	*name;
    term_t (*fn)(int, term_t *, void *);
    void *arg;
};

static struct fn_info symbolfunc_table[] = {
    /* Core theory */
    { "not", eval_unary, yices_not },
    { "and", eval_nary, yices_and },
    { "or", eval_nary, yices_or },
    { "xor", eval_nary, yices_xor },
    { "=>", eval_binary_right_assoc, yices_implies },
    { "iff", eval_binary, yices_iff },
    { "=", eval_binary, yices_eq },
    { "/=", eval_binary, yices_neq },
    { "distinct", eval_nary, yices_distinct },
    { "ite", eval_trinary, yices_ite },
    /* Ints theory */
    { "+", eval_nary, yices_sum },
    { "-", eval_minus, 0 },
    { "*", eval_nary, yices_product },
    { "mod", 0, 0 },
    { "div", 0, 0 },
    { "abs", 0, 0 },
    { "<", eval_binary_left_and, yices_arith_lt_atom },
    { ">", eval_binary_left_and, yices_arith_gt_atom },
    { "<=", eval_binary_left_and, yices_arith_leq_atom },
    { ">=", eval_binary_left_and, yices_arith_geq_atom },
    /* Reals theory */
    { "/", eval_binary, yices_div },
    /* Reals_Ints theory */
    { "to_real", 0, 0 },
    { "to_int", 0, 0 },
    { "is_int", 0, 0 },
    /* ArraysEx theory */
    { "select", eval_select, 0 },
    { "store", eval_store, yices_update },
    /* Fixed_Size_BitVectors theory */
    { "concat", eval_binary, yices_bvconcat },
    { "bvnot", eval_unary, yices_bvnot },
    { "bvneg", eval_unary, yices_bvneg },
    { "bvand", eval_binary_left_assoc, yices_bvand },
    { "bvor", eval_binary_left_assoc, yices_bvor },
    { "bvxor", eval_binary_left_assoc, yices_bvxor },
    { "bvnand", eval_binary, yices_bvnand },
    { "bvnor", eval_binary, yices_bvnor },
    { "bvxnor", eval_binary, yices_bvxnor },
    { "bvadd", eval_binary_left_assoc, yices_bvadd },
    { "bvsub", eval_binary, yices_bvsub },
    { "bvmul", eval_binary_left_assoc, yices_bvmul },
    { "bvudiv", eval_binary, yices_bvdiv },
    { "bvurem", eval_binary, yices_bvrem },
    { "bvshl", eval_binary, yices_bvshl },
    { "bvsdiv", eval_binary, yices_bvsdiv },
    { "bvsrem", eval_binary, yices_bvsrem },
    { "bvsmod", eval_binary, yices_bvsmod },
    { "bvlshr", eval_binary, yices_bvlshr },
    { "bvashr", eval_binary, yices_bvashr },
    { "bvult", eval_binary_left_and, yices_bvlt_atom },
    { "bvule", eval_binary_left_and, yices_bvle_atom },
    { "bvugt", eval_binary_left_and, yices_bvgt_atom },
    { "bvuge", eval_binary_left_and, yices_bvge_atom },
    { "bvslt", eval_binary_left_and, yices_bvslt_atom },
    { "bvsle", eval_binary_left_and, yices_bvsle_atom },
    { "bvsgt", eval_binary_left_and, yices_bvsgt_atom },
    { "bvsge", eval_binary_left_and, yices_bvsge_atom },
};
#define ALEN(A)	((int)(sizeof(A)/sizeof(A[0])))

void eval_init()
{
    int i;
    // Core theory
    yices_set_type_name(yices_bool_type(), cached_string("Bool"));
    yices_set_term_name(yices_true(), cached_string("true"));
    yices_set_term_name(yices_false(), cached_string("false"));
    // Ints theory
    yices_set_type_name(yices_int_type(), cached_string("Int"));
    // Reals theory
    yices_set_type_name(yices_real_type(), cached_string("Real"));
    symbolfunc = new_hashmap(ptrhash, ptrcmp, 10);
    for (i = 0; i < ALEN(symbolfunc_table); i++) {
	symbolfunc_table[i].name = cached_string(symbolfunc_table[i].name);
	hashmap_insert(symbolfunc, symbolfunc_table[i].name,
		       &symbolfunc_table[i], 0); }
}

value_t eval_sexpr(value_t fn, int ac, value_t *av)
{
    value_t rv;
    term_t temp[64], *args = temp, t;
    int i;
    if (ac > 64)
	args = malloc(ac * sizeof(term_t));
    yices_clear_error();
    for (i = 0; i < ac; i++) {
	if (av[i].tag == vtTERM)
	    args[i] = av[i].v.term;
	else if (av[i].tag == vtSYMBOL)
	    args[i] = yices_get_term_by_name(av[i].v.str);
	else
	    args[i] = NULL_TERM;
	if (yices_error_code()) {
	    yices_print_error(stderr);
	    yices_clear_error(); } }
    rv.tag = vtUNKNOWN;
    switch (fn.tag) {
    case vtSYMBOL:
	if ((t = yices_get_term_by_name(fn.v.str)) != NULL_TERM) {
	    rv.tag = vtTERM;
	    rv.v.term = yices_application(t, ac, args);
	} else {
	    const struct fn_info *info = hashmap_lookup(symbolfunc, fn.v.str, 0);
	    if (info && info->fn) {
		rv.tag = vtTERM;
		rv.v.term = info->fn(ac, args, info->arg); } }
	break;
    case vtTERM:
	rv.tag = vtTERM;
	rv.v.term = yices_application(fn.v.term, ac, args);
	break;
    case vtEXTRACT:
	assert(ac == 1);
	rv.tag = vtTERM;
	// yices and smt2 swap the meanings of 'i' and 'j' here...
	assert(fn.v.fn.i1 <= fn.v.fn.i0);
	rv.v.term = yices_bvextract(args[0], fn.v.fn.i1, fn.v.fn.i0);
	break;
    case vtSIGN_EXTEND:
	assert(ac == 1);
	rv.tag = vtTERM;
	rv.v.term = yices_sign_extend(args[0], fn.v.fn.i0);
	break;
    case vtREPEAT:
	assert(ac == 1);
	rv.tag = vtTERM;
	rv.v.term = yices_bvrepeat(args[0], fn.v.fn.i0);
	break;
    case vtZERO_EXTEND:
	assert(ac == 1);
	rv.tag = vtTERM;
	rv.v.term = yices_zero_extend(args[0], fn.v.fn.i0);
	break;
    case vtROTATE_LEFT:
	assert(ac == 1);
	rv.tag = vtTERM;
	rv.v.term = yices_rotate_left(args[0], fn.v.fn.i0);
	break;
    case vtROTATE_RIGHT:
	assert(ac == 1);
	rv.tag = vtTERM;
	rv.v.term = yices_rotate_right(args[0], fn.v.fn.i0);
	break;
    default:
	break; }
    if (rv.tag == vtUNKNOWN) {
	fprintf(stderr, "%d:FIXME -- Eval failed: ", lineno);
	print_value(stderr, fn);
	fprintf(stderr, "\n"); }
    if (rv.tag == vtTERM && rv.v.term == NULL_TERM) {
	yyerror("%d:FIXME -- Eval got NULL_TERM", lineno);
	fprintf(stderr, "    (");
	print_value(stderr, fn);
	for (i = 0; i < ac; i++) {
	    fprintf(stderr, " ");
	    print_value(stderr, av[i]); }
	fprintf(stderr, ")\n"); }
    if (yices_error_code()) {
	yices_print_error(stderr);
	yices_clear_error(); }
    if (ac > 64)
	free(args);
    return rv;
}

void print_value(FILE *fp, value_t val)
{
    switch (val.tag) {
    case vtUNKNOWN: fprintf(fp, "UNKNOWN"); break;
    case vtTERM:
	if (val.v.term != NULL_TERM)
	    yices_pp_term(fp, val.v.term, 999, 0, 0);
	else
	    fprintf(fp, "NULL_TERM");
	break;
    case vtSORT:
	if (val.v.term != NULL_TYPE)
	    yices_pp_type(fp, val.v.sort, 999, 0, 0);
	else
	    fprintf(fp, "NULL_TYPE");
	break;
    case vtSYMBOL:
	fprintf(fp, "|%s|", val.v.str);
	break;
    case vtSTRING:
	fprintf(fp, "\"%s\"", val.v.str);
	break;
    case vtEXTRACT:
	fprintf(fp, "(_ extract %d %d)", val.v.fn.i0, val.v.fn.i1);
	break;
    case vtSIGN_EXTEND:
	fprintf(fp, "(_ sign_extend %d)", val.v.fn.i0);
	break;
    case vtREPEAT:
	fprintf(fp, "(_ repeat %d)", val.v.fn.i0);
	break;
    case vtROTATE_LEFT:
	fprintf(fp, "(_ rotate_left %d)", val.v.fn.i0);
	break;
    case vtROTATE_RIGHT:
	fprintf(fp, "(_ rotate_right %d)", val.v.fn.i0);
	break;
    case vtZERO_EXTEND:
	fprintf(fp, "(_ zero_extend %d)", val.v.fn.i0);
	break;
    }
}

type_t indexed_type(const char *sym, int idxcnt, int *idx)
{
    // FIXME -- the only valid indexed type is BitVec and it only has one index
    if (idxcnt == 1 && !strcmp(sym, "BitVec"))
	return yices_bv_type(idx[0]);
    char tmp[256], *p = tmp, *end = tmp + sizeof(tmp);
    int i;
    for (i = 0; i < idxcnt && p < end; i++)
	p += snprintf(p, end-p, " %d", idx[i]);
    yyerror("Unknown indexed type (_ %s%s)", sym, tmp);
    return NULL_TYPE;
}

value_t indexed_value(const char *sym, int idxcnt, int *idx)
{
    unsigned long val;
    int i;
    if (idxcnt == 1 && sscanf(sym, "bv%lu%n", &val, &i) >= 1 && sym[i] == 0) {
	if (idx[0] > 64 && strlen(sym) > 21) {
	    /* constant too big for unsigned long */
	    mpz_t val;
	    value_t rv;
	    mpz_init_set_str(val, sym+2, 10);
	    rv = TERMval(yices_bvconst_mpz(idx[0], val));
	    mpz_clear(val);
	    return rv; }
	return TERMval(yices_bvconst_uint64(idx[0], val)); }
    if (idxcnt == 2 && !strcmp(sym, "extract"))
	return FNval(vtEXTRACT, idx[0], idx[1]);
    if (idxcnt == 1 && !strcmp(sym, "sign_extend"))
	return FNval(vtSIGN_EXTEND, idx[0], 0);
    if (idxcnt == 1 && !strcmp(sym, "zero_extend"))
	return FNval(vtZERO_EXTEND, idx[0], 0);
    if (idxcnt == 1 && !strcmp(sym, "rotate_left"))
	return FNval(vtROTATE_LEFT, idx[0], 0);
    if (idxcnt == 1 && !strcmp(sym, "rotate_right"))
	return FNval(vtROTATE_RIGHT, idx[0], 0);
    if (idxcnt == 1 && !strcmp(sym, "repeat"))
	return FNval(vtREPEAT, idx[0], 0);
    if (idxcnt == 1 && !strcmp(sym, "divisible")) {
	yyerror("FIXME -- add divisible support");
	return UNKNOWNval(); }
    char tmp[256], *p = tmp, *end = tmp + sizeof(tmp);
    for (i = 0; i < idxcnt && p < end; i++)
	p += snprintf(p, end-p, " %d", idx[i]);
    yyerror("Unknown indexed term (_ %s%s)", sym, tmp);
    return UNKNOWNval();
}
