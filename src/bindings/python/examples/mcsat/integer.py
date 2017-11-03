#!/usr/bin/env python

from ctypes import ( c_int64 )

from yices import *

"""

iv7:Integer > (0).Integer 
and 
( iv8:Integer === iv1:Integer * iv7:Integer 
  and 
  ( iv3:Integer - iv8:Integer === iv5:Integer 
    and 
    ( iv5:Integer >= (0).Integer 
      and ( iv9:Integer === iv1:Integer * iv7:Integer 
            and ( iv4:Integer - iv9:Integer === iv6:Integer 
                  and 
                  ( iv6:Integer >= (0).Integer 
                    and ( iv1:Integer === (1).Integer 
                          and ( iv2:Integer === (0).Integer 
                                and ( iv3:Integer === (100).Integer 
                                      and ( iv4:Integer === (100).Integer 
                                            and (true).Boolean))))))))))

simplifies by hand to:

iv7:Integer > 0
and 
iv8:Integer === iv1:Integer * iv7:Integer 
and 
iv3:Integer - iv8:Integer === iv5:Integer 
and 
iv5:Integer >= 0
and 
iv9:Integer === iv1:Integer * iv7:Integer 
and 
iv4:Integer - iv9:Integer === iv6:Integer 
and 
iv6:Integer >= 0
and 
iv1:Integer === 1
and 
iv2:Integer === 0
and 
iv3:Integer === 100
and 
iv4:Integer === 100 

and translates to:

(and (> x7 0) 
     (= x8 (* x1 x2))
     (= x5 (- x3 x8))
     (> x5 0)
     (= x9 (* x1 x7))
     (= x6 (- x4 x9))
     (>= x6 0)
     (= x1 1)
     (= x2 0)
     (= x3 100)
     (= x4 100))

"""



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


def solve_problem():
	problem = """
(and (> x7 0) 
     (= x8 (* x1 x2))
     (= x5 (- x3 x8))
     (> x5 0)
     (= x9 (* x1 x7))
     (= x6 (- x4 x9))
     (>= x6 0)
     (= x1 1)
     (= x2 0)
     (= x3 100)
     (= x4 100)
    )
"""
	variables = [None] * 10
	values = [None] * 10
	
	for i in range(1, 10):
		variables[i] = declare_integer_var('x{0}'.format(i))
		
	p = yices_parse_term(problem)
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


	
	print "\nValues of variables:\n"

	i64 = c_int64()

	for i in range(1, 10):
		yices_get_int64_value(model, variables[i], i64)
		values[i] = i64.value
		print "x{0} = {1}".format(i, values[i])

	# cleanup
	yices_free_model(model)
	yices_free_context(ctx)



def main(args):
    if yices_has_mcsat():
        yices_init()
        solve_problem()
        yices_exit()

    print '\nbye\n'



if __name__ == '__main__':
    sys.exit(main(sys.argv))
