#!/usr/bin/env python

from ctypes import ( c_int64 )

from yices import *

from yiceslib import (term_to_string, declare_real_var, declare_integer_var, make_context)

#
# Work in progress: Not clear (currently impossible?) how to do an EF using the API.
#

"""
Formula:
the negation of:
Forall:
tt(10) t(11)... tt(24), tw(1), tw(2)
Exists
tt(1010) tt(1011) ... tt(1024)
Formula body
tt(24) === tt(1024) 
and 
(tt(22) === tt(1022) 
and 
(tt(21) === tt(1021) 
and 
(tt(19) === tt(1019) 
and 
(tt(16) === tt(1016) 
and 
(tt(15) === tt(1015) 
and 
(tt(14) === tt(1014) 
and 
(tt(13) === tt(1013) 
and 
(tt(12) === tt(1012) 
and 
(tt(10) === tt(1010) 
and 
(tt(24) === tt(22) + tw(1) 
and 
(tt(24) >= (0/1).Real 
and 
(tt(24) >= tt(23) 
and 
(tt(23) >= tt(22) 
and 
(tt(22) >= tt(21)
and 
(tt(21) >= tt(20) 
and 
(tt(20) >= tt(19) 
and 
(tt(19) === tt(16) + tw(1) + tw(2) 
and 
(tt(19) >= (0/1).Real 
and 
(tt(19) >= tt(18) 
and 
(tt(18) >= tt(17)
and 
(tt(17) >= tt(16) 
and 
(tt(16) >= tt(15) 
and 
(tt(15) >= tt(14) 
and 
(tt(14) >= tt(13) 
and 
(tt(13) >= tt(12) 
and 
(tt(12) >= tt(11) 
and 
(tt(11) >= tt(10) 
and 
((0/1).Real >= (0/1).Real 
and 
tt(10) >= (0/1).Real 
and 
(tw(1) >= (1/1).Real 
and 
(tw(2) >= (4/1).Real 
and 
(true).Boolean))))))))))))))))))))

and 

(tt(1024) === tt(1022) + tw(1) 
and 
(tt(1024) >= (0/1).Real 
and 
(tt(1024) >= tt(1023) 
and 
(tt(1023) >= tt(1022) 
and 
(tt(1022) >= tt(1021) 
and 
(tt(1021) >= tt(1020) 
and 
(tt(1020) >= tt(1019) 
and 
(tt(1019) === tt(1016) + tw(1) + tw(2) 
and 
(tt(1019) >= (0/1).Real 
and 
(tt(1019) >= tt(1018) 
and 
(tt(1018) >= tt(1017) 
and 
(tt(1017) >= tt(1016) 
and 
(tt(1016) >= tt(1015) 
and 
(tt(1015) >= tt(1014) 
and 
(tt(1014) >= tt(1013) 
and 
(tt(1013) >= tt(1012) 
and
(tt(1012) >= tt(1011) 
and 
(tt(1011) >= tt(1010) 
and 
((0/1).Real >= (0/1).Real 
and 
tt(10) >= (0/1).Real 
and 
(tw(1) >= (1/1).Real 
and 
(tw(2) >= (4/1).Real 
and 
(true).Boolean)))))))))))))))))))))))))))))))


see v.ys or below for the translation.



"""

def solve_problem():
	problem = """

 (forall (tt1010 :: real
		 tt1011 :: real
		 tt1012 :: real
		 tt1013 :: real
		 tt1014 :: real
		 tt1015 :: real
		 tt1016 :: real
		 tt1017 :: real
		 tt1018 :: real
		 tt1019 :: real
		 tt1020 :: real
		 tt1021 :: real
		 tt1022 :: real
		 tt1023 :: real
		 tt1024 :: real
		 )
	 (not 
	  (and 
	   (= tt24 tt1024)
	   (= tt22 tt1022)
	   (= tt21 tt1021)
	   (= tt19 tt1019)
	   (= tt16 tt1016)
	   (= tt15 tt1015)
	   (= tt14 tt1014)
	   (= tt13 tt1013)
	   (= tt12 tt1012)
	   (= tt10 tt1010)
	   (= tt24 (+ tt22 tw1))
	   (>= tt24 0)
	   (>= tt24 tt23)
	   (>= tt23 tt22)
	   (>= tt22 tt21)
	   (>= tt21 tt20)
	   (>= tt20 tt19)
	   (= tt19 (+ tt16 tw1 tw2)) 
	   (>= tt19 0)
	   (>= tt19 tt18) 
	   (>= tt18 tt17)
	   (>= tt17 tt16)
	   (>= tt16 tt15)
	   (>= tt15 tt14)
	   (>= tt14 tt13)
	   (>= tt13 tt12)
	   (>= tt12 tt11)
	   (>= tt11 tt10)
	   (>= 0 0)
	   (>= tt10 0)
	   (>= tw1 1)
	   (>= tw2 4)
	   (= tt1024 (+ tt1022 tw1))
	   (>= tt1024 0)
	   (>= tt1024 tt1023)
	   (>= tt1023 tt1022)
	   (>= tt1022 tt1021)
	   (>= tt1021 tt1020)
	   (>= tt1020 tt1019)
	   (= tt1019 (+ tt1016 tw1 tw2))
	   (>= tt1019 0)
	   (>= tt1019 tt1018)
	   (>= tt1018 tt1017)
	   (>= tt1017 tt1016)
	   (>= tt1016 tt1015)
	   (>= tt1015 tt1014)
	   (>= tt1014 tt1013)
	   (>= tt1013 tt1012)
	   (>= tt1012 tt1011)
	   (>= tt1011 tt1010)
	   (>= 0 0)
	   (>= tt10 0)
	   (>= tw1 1)
	   (>= tw2 4)
	   )
	  )
	 )
"""

	
	for i in range(10, 25):
		declare_real_var('tt{0}'.format(i))

	for i in range(1, 3):
		declare_real_var('tw{0}'.format(i))
		
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
