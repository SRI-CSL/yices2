

from yices import *


def term_to_string(term):
    """Convert a term to a string."""
    return yices_term_to_string(term, 80, 20, 0)


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



def parse_k_and_d():

    fail =  (False, None, None)

    if len(sys.argv) != 3:
        usage = "{0} <K a float> <D a float>\n"
        print usage.format(sys.argv[0])
        return fail

    k = sys.argv[1]
    d = sys.argv[2]

    try:
        pk = float(k)
    except:
        print "K must be a non zero floating point"
        return fail
    try:
        pd = float(d)
    except:
        print "D must be a non zero floating point"
        return fail


    return (True, k, d)


__status2string = {
    STATUS_IDLE : 'STATUS_IDLE',
    STATUS_SEARCHING : 'STATUS_SEARCHING',
    STATUS_UNKNOWN : 'STATUS_UNKNOWN',
    STATUS_SAT : 'STATUS_SAT',
    STATUS_UNSAT : 'STATUS_UNSAT',
    STATUS_INTERRUPTED : 'STATUS_INTERRUPTED',
    STATUS_ERROR : 'STATUS_ERROR',
}

def status2string(status):
    if status in __status2string:
        return __status2string[status]
    else:
        return 'Unknown status'
