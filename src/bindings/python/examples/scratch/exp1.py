#!/usr/bin/env python

"""

use discrete ranges here just to get going.

b: is the (log of the) number of bits in a symbol; b in (2, 3, 4, 5, 6, 7, 8)

t: is the symbol transmission length in (milli?) seconds; t in (10, 20, 30, 40) say.

e: is the error rate;  e = K * (b/t)  say.


re: yices2/examples/example_mcsat.c


"""

import sys

from yices import *

from ylib import *

class Solver(object):

    BITRANGE = (2, 3, 4, 5, 6, 7, 8)

    TRANGE = (10, 20, 30, 40)

    # k is the constant of proportionality
    #
    # e * t = k * b
    #
    def __init__(self, k, d):
        yices_init()


        #just make e, b and t for now
        int_t = yices_int_type()
        real_t = yices_real_type()

        self.k =  yices_parse_float(k)
        self.d =  yices_parse_float(d)

        self.b =  declare_var('b', int_t)
        self.t =  declare_var('t', int_t)
        self.e =  declare_var('e', real_t)

        self.brange = [ yices_int32(i) for i in Solver.BITRANGE ]
        self.trange = [ yices_int32(i) for i in Solver.TRANGE ]







    def exit(self):
        yices_exit()




    def generateConstraints(self, context):
        # add the generic facts:
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
            t = make_empty_term_array(n);
            for i in xrange(n):
                t[i] = yices_eq(x, rng[i])
            return yices_or(n, t)

        yices_assert_formula(context, in_range(self.b, self.brange))
        yices_assert_formula(context, in_range(self.t, self.trange))
        yices_assert_formula(context, yices_eq(yices_mul(self.e, self.t), yices_mul(self.k, self.b)))
        yices_assert_formula(context, yices_arith_lt_atom(self.e, self.d))

    def print_model(self, model):
        int32_val = c_int32()
        double_val = c_double()

        yices_get_int32_value(model, self.b, int32_val)
        print '\tb = {0}'.format(int32_val.value)
        yices_get_int32_value(model, self.t, int32_val)
        print '\tt = {0}'.format(int32_val.value)
        yices_get_double_value(model, self.e, double_val);
        print ('\te = {0}\n'.format(double_val.value))



    def solve(self):
        retval = False
        context = make_context()

        self.generateConstraints(context)


        smt_stat = yices_check_context(context, None)
        if smt_stat != STATUS_SAT:
            print 'No solutions: smt_stat = {0}\n'.format(smt_stat)
        else:
            model = yices_get_model(context, 1)
            #self.print_model(model)
            retval =  True

        yices_free_context(context)
        return retval



    def countSolutions(self):
        retval = 0

        negated_diagrams = []

        def model2term(model):
            termlist = []
            val = c_int32()
            for var in (self.b, self.t):
                yices_get_int32_value(model, var, val)
                termlist.append(yices_arith_eq_atom(var, yices_int32(val.value)))
            return yices_and(len(termlist), make_term_array(termlist))


        while True:

            context = make_context()
            self.generateConstraints(context)
            for phi in negated_diagrams:
                yices_assert_formula(context, phi)

            smt_stat = yices_check_context(context, None)
            if smt_stat != STATUS_SAT:
                break
            else:
                model = yices_get_model(context, 1)
                print 'Solution {0}:\n'.format(retval)
                self.print_model(model)
                diagram = model2term(model)
                negated_diagrams.append(yices_not(diagram))
                retval += 1



            yices_free_context(context)



        return retval


def main():

    #<argument parsing>
    if len(sys.argv) != 3:
        usage = "{0} <K a float> <D a float>\n"
        print usage.format(sys.argv[0])
        return 1

    k = sys.argv[1]
    d = sys.argv[2]

    try:
        pk = float(k)
    except:
        print "K must be a non zero floating point"
        return 1
    try:
        pd = float(d)
    except:
        print "D must be a non zero floating point"
        return 1
    #</argument parsing>

    solver = Solver(k, d)

    if solver.solve():
        solver.countSolutions()

    solver.exit()

    return 0



if __name__ == '__main__':
    sys.exit(main())
