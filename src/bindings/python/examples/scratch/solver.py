import sys

from yices import *

from ylib import *

class Solver(object):
    """
    This solver implements BD's suggestion:

        Let x be a vector of integer and real variables. Suppose we want to
        solve a set of constraints C[x] while minimizing the value of F[x].
        
        One simple strategy is to first find an initial solution x0 to C:
    
        C[x0]
    
        then iteratively find x1, x2, x3, x4 ....
    
        such that
    
        C[x{n+1}]  and F(x{n+1}) < F(xn) - delta
    
        for some suitable delta.

    We do it parametrically in order to decouple the algorithm actual from 
    the particular choice of C and F that we use in the example exp2.py.

"""


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
                value = yices_get_value_as_term(model, self.F)
                if self.DEBUG:
                    double_val = c_double()
                    yices_get_double_value(model, self.F, double_val)
                    print 'Bound = {0}   (i.e. {1})\n'.format(term_to_string(value), double_val.value)
                return yices_and2(self.C, yices_arith_lt_atom(self.F, value))

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
    
