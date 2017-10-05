

from yices import *



#declare_var("x", yices_real_type())
def declare_var(name, sort):
    """Creates a real variable."""
    try:
        x = yices_new_uninterpreted_term(sort)
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
