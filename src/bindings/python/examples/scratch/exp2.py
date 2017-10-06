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


    def __init__(self, C, F, delta):
        """ Initializes the solver.
        
            - C is a boolean yices term
            - F is a real valued yices term
            - delta is a yices double constant

        """

        self.DEBUG = False
        
        
        
        self.C = C
        self.F = F
        self.delta = delta

        print 'C = {0}\nF={1}\ndelta = {2}'.format(term_to_string(self.C), term_to_string(self.F), term_to_string(self.delta))

        
    def solve(self, Phi):
        """ Attempts to solve the constraint Phi. 

        Returns either None or a model that satisfies Phi.
        """
        model = None
        context = make_context()

        yices_assert_formula(context, Phi)


        smt_stat = yices_check_context(context, None)

        if smt_stat != STATUS_SAT:
            if self.DEBUG:
                print 'The term:\n{0}\n has NO solutions: smt_stat = {1}\n'.format(term_to_string(Phi), status2string(smt_stat))
        else:
            model = yices_get_model(context, 1)
            if self.DEBUG:
                print "Model:\n"
                yices_pp_model_fd(1, model, 80, 20, 0)

        yices_free_context(context)
        return model


    def iterate(self):
        iteration = 0

        model = None
        bound = None
        double_val = c_double()

        
        def makeConstraint(model):
            if model is None:
                return self.C
            else:
                bound = yices_get_double_value(model, self.F, double_val)
                b = yices_parse_float('{0}'.format(bound))
                if self.DEBUG:
                    print 'Bound = {0}\n'.format(double_val.value)
                return yices_and2(self.C, yices_arith_lt_atom(self.F, b))

        while True:
            phi = makeConstraint(model)
            next_model = self.solve(phi)
            if next_model is not None:
                if model is not None:
                    yices_free_model(model)
                model = next_model
                iteration += 1
            else:
                break
        if model is not None:
            print 'Iteration: {0}\n'.format(iteration)
            yices_pp_model_fd(1, model, 80, 20, 0)

        return model
    
            
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



    solver = Solver(C, F, d)

    
    solution = solver.iterate()


    if solution is not None:
        yices_free_model(solution)
    
    yices_exit()

 
    return 0


if __name__ == '__main__':
    sys.exit(main())
    

        
