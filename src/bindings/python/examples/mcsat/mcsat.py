#!/usr/bin/env python

from yices import *


def term_to_string(term):
    """Convert a term to a string."""
    return yices_term_to_string(term, 80, 20, 0)

def declare_var(name):
    """Creates a real variable."""
    try:
        x = yices_new_uninterpreted_term(yices_real_type())
        yices_set_term_name(x, name)
        return x
    except YicesException as e:
        print 'declare_var: ', e
        return None


def make_context():
    """Create a QF_NRA, non-linear real arithmetic, context."""
    cfg = yices_new_config()
    yices_default_config_for_logic(cfg, 'QF_NRA')
    yices_set_config(cfg, 'mode', 'one-shot')
    ctx = yices_new_context(cfg)
    yices_free_config(cfg)
    return ctx


def show_algebraic_value(model, term):
    alg = lp_algebraic_number_t()
    yices_get_algebraic_number_value(model, term, alg)
    lp_algebraic_number_print(alg, 1)  # 1 is stdout
    lp_algebraic_number_destruct(alg)


def test_mcsat():
    x = declare_var('x');
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

    # FIXME: libpoly python API is not part of yices.py
    #    print "algebraic value of x = "
    #    show_algebraic_value(model, x)
    #    print "\n"

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
