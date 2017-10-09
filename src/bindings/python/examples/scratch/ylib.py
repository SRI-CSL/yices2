

from yices import *

#iam: work in progress (this is no longer needed, but may one day be useful)
def yices_evalute_term(model, term):
    yval = yval_t()
    try: 
        yices_get_value(model, term, yval)
        print 'yices_evalute_term: term is of type {0}'.format(node_tag2string(yval.node_tag))
        tag = yval.node_tag
        if tag == YVAL_UNKNOWN:
            return None
        elif tag == YVAL_BOOL:
            i32 = c_int32()
            yices_val_get_bool(model, yval, i32)
            return True if i32.value else False
        elif tag == YVAL_RATIONAL:
            i64 = c_int64()
            #iam: does 32 => 64? (i.e. do I need the disjuncton?)
            if yices_val_is_int64(model, yval) or yices_val_is_int32(model, yval):
                yices_val_get_int64(model, yval, i64)
                return i64.val
            #elif yices_val_is_rational32(model, yval):
            #    pass
            #elif yices_val_is_rational64(model, yval):
            #    pass
            else:
                double_val = c_double()
                yices_val_get_double(model, yval, double_val)
                return double_val.value
        elif tag == YVAL_ALGEBRAIC:
            pass
        elif tag == YVAL_BV:
            pass
        elif tag == YVAL_SCALAR:
            pass
        elif tag == YVAL_TUPLE:
            pass
        elif tag == YVAL_FUNCTION:
            pass
        elif tag == YVAL_MAPPING:
            pass
        else:
            pass
        return None
    except YicesException as e:
        print 'yices_evalute_term: ', e
        return None





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


__node_tag2string = {
    YVAL_UNKNOWN: 'YVAL_UNKNOWN',
    YVAL_BOOL: 'YVAL_BOOL',
    YVAL_RATIONAL: 'YVAL_RATIONAL',
    YVAL_ALGEBRAIC: 'YVAL_ALGEBRAIC',
    YVAL_BV: 'YVAL_BV',
    YVAL_SCALAR: 'YVAL_SCALAR',
    YVAL_TUPLE: 'YVAL_TUPLE',
    YVAL_FUNCTION: 'YVAL_FUNCTION',
    YVAL_MAPPING: 'YVAL_MAPPING',
    }

def node_tag2string(node_tag):
    if node_tag in __node_tag2string:
        return __node_tag2string[node_tag]
    else:
        return 'Unknown node_tag'
