from ctypes import ( c_int64 )

from yices import *


def term_to_string(term):
    """Convert a term to a string."""
    return yices_term_to_string(term, 80, 20, 0)

def declare_real_var(name):
    """Creates a real variable with given name."""
    try:
        x = yices_new_uninterpreted_term(yices_real_type())
        yices_set_term_name(x, name)
        return x
    except YicesException as e:
        print 'declare_real_var: ', e
        return None

def declare_integer_var(name):
    """Creates an integer variable with given name."""
    try:
        x = yices_new_uninterpreted_term(yices_int_type())
        yices_set_term_name(x, name)
        return x
    except YicesException as e:
        print 'declare_integer_var: ', e
        return None


def make_context():
    """Create a QF_NRA, non-linear real arithmetic, context."""
    cfg = yices_new_config()
    yices_default_config_for_logic(cfg, 'QF_NRA')
    yices_set_config(cfg, 'mode', 'one-shot')
    ctx = yices_new_context(cfg)
    yices_free_config(cfg)
    return ctx

