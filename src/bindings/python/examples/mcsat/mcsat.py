#!/usr/bin/env python

from yices import *

from yiceslib import (term_to_string, declare_real_var, declare_integer_var, make_context)



def show_algebraic_value(model, term):
    alg = lp_algebraic_number_t()
    yices_get_algebraic_number_value(model, term, alg)
    # FIXME: libpoly python API is not part of yices.py
    #lp_algebraic_number_print(alg, 1)  # 1 is stdout
    #lp_algebraic_number_destruct(alg)


def test_mcsat():
    x = declare_real_var('x');
    p = yices_parse_term('(= (* x x) 2)')
    s = term_to_string(p)
    print 'Assertion: {0}\n'.format(s)
    ctx = make_context()
    yices_assert_formula(ctx, p)

    status = yices_check_context(ctx, None)
    if status != STATUS_SAT:
        print 'Test failed: status = {0} != STATUS_SAT\n'.format(status)

    print 'Satisfiable!\n'

    model = yices_get_model(ctx, 1)

    print "Model:\n"
    yices_pp_model_fd(1, model, 80, 20, 0)


    #print "algebraic value of x = "
    #show_algebraic_value(model, x)
    #print "\n"

    print "Test succeeded\n"

    # cleanup
    yices_free_model(model)
    yices_free_context(ctx)



def main(args):
    if yices_has_mcsat():
        yices_init()
        test_mcsat()
        yices_exit()

    print 'bye'



if __name__ == '__main__':
    sys.exit(main(sys.argv))
