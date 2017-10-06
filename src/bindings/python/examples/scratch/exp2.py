#!/usr/bin/env python

"""

In this example we implement BD's suggestion:

    Let x be a vector of integer and real variables. Suppose we want to
    solve a set of constraints C[x] while minimizing the value of F[x].
    
    One simple strategy is to first find an initial solution x0 to C:

    C[x0]

    then iteratively find x1, x2, x3, x4 ....

    such that

    C[x{n+1}]  and F(x{n+1}) < F(xn) - delta

    for some suitable delta.

We do it parametrically in order to decouple the algorithm actual from 
the particular choice of C and F that we use in this example.

    

"""



import sys

from yices import *

from ylib import *

class Solver(object):


    def __init__(self, C, F, delta, e):
        """ Initializes the solver.
        
            - C is a boolean yices term
            - F is a real valued yices term
            - delta is a yices double constant

        """
        self.C = C
        self.F = F
        self.delta = delta
        self.e = e

        
    def solve(self, Phi):
        """ Attempts to solve the constraint Phi. 

        Returns either None or a model that satisfies Phi.
        """
        model = None
        context = make_context()

        yices_assert_formula(context, Phi)


        smt_stat = yices_check_context(context, None)

        if smt_stat != STATUS_SAT:
            fmla = term_to_string(Phi)
            print 'The term:\n{0}\n has NO solutions: smt_stat = {1}\n'.format(fmla, status2string(smt_stat))
        else:
            model = yices_get_model(context, 1)
            if True:
                print "Model:\n"
                yices_pp_model_fd(1, model, 80, 20, 0)

        yices_free_context(context)
        return model


    def iterate(self):
        print '1, 2, 3, 4...'
        model = self.solve(self.C)
        bound = None
        double_val = c_double()
        yval_val = yval_t()

        if model is not None:
            #HERE
            #BD: works with e
            bound =  yices_get_value(model, self.e, yval_val)
            #does not work with F
            #bound =  yices_get_value(model, self.F, yval_val)
            print 'Bound (node tag = {0})\n'.format(yval_val.node_tag)
        
    
def main():

    (ok, pk, pd) = parse_k_and_d()

    if not ok:
        print 'Try ./exp2.py 2 0.4'
        return 1

    yices_init()

    #Need to make C, F, and delta.

    k =  yices_parse_float(pk)
    d =  yices_parse_float(pd)

    #just make e, b and t for now
    int_t = yices_int_type()
    real_t = yices_real_type()
        
    b =  declare_var('b', int_t)
    t =  declare_var('t', int_t)
    e =  declare_var('e', real_t)


    BITRANGE = (2, 3, 4, 5, 6, 7, 8)

    TRANGE = (10, 20, 30, 40)

    brange = [ yices_int32(i) for i in BITRANGE ]
    trange = [ yices_int32(i) for i in TRANGE ]
    
    # C is the conjuction of 
    #
    # b is in bit_range
    # t is in time_range
    # e * t = k * b
    # e < d
    #
    #
    #  x is in the given range
    def in_range(x, rng):
        n = len(rng)
        t = make_empty_term_array(n)
        for i in xrange(n):
            t[i] = yices_eq(x, rng[i])
        return yices_or(n, t)

    
    c = make_empty_term_array(4)

    c[0] = in_range(b, brange)
    c[1] = in_range(t, trange)
    c[2] = yices_eq(yices_mul(e, t), yices_mul(k, b))
    c[3] = yices_arith_lt_atom(e, d)

    C = yices_and(4, c)

    #
    #  f is the value we want to minimize.
    #  It is the sum of:
    #
    #  100 * t
    #  144 / b
    #  e
    #
    #
    #
    f = make_empty_term_array(3)

    f[0] = yices_mul(yices_int32(100), t)
    f[1] = yices_division(yices_int32(144), b)
    f[2] = e

    F = yices_sum(3, f)
    

    solver = Solver(C, f, d, e)

    
    solver.iterate()

    
    yices_exit()

 
    return 0


if __name__ == '__main__':
    sys.exit(main())
    

        
