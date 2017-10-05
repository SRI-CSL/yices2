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
        
        self.b =  yices_new_uninterpreted_term(int_t)
        self.t =  yices_new_uninterpreted_term(int_t)
        self.e =  yices_new_uninterpreted_term(real_t)

        self.brange = [ yices_int32(i) for i in Solver.BITRANGE ]
        self.trange = [ yices_int32(i) for i in Solver.TRANGE ]

        config = yices_new_config()
        # set the logic to QF_NRA and mode to "one-shot"
        # (one-shot is currently required when MCSAT is used).
        yices_default_config_for_logic(config, "QF_NRA")
        yices_set_config(config, "mode", "one-shot")
        # the context (a set/stack of yices assertions)
        self.context = yices_new_context(config)

        yices_free_config(config)


        # add the generic facts:
        #
        # b is in bit_range
        # t is in time_range
        # e * t = k * b
        # e < d
        self.generateConstraints()


        

    def exit(self):
        if self.context:
            yices_free_context(self.context)
        yices_exit()


    def generateConstraints(self):
        #  x is in the given range
        def in_range(x, rng):
            n = len(rng)
            t = make_empty_term_array(n);
            for i in xrange(n):
                t[i] = yices_eq(x, rng[i])
            return yices_or(n, t)
        
        yices_assert_formula(self.context, in_range(self.b, self.brange))
        yices_assert_formula(self.context, in_range(self.t, self.trange))
        yices_assert_formula(self.context, yices_eq(yices_mul(self.e, self.t), yices_mul(self.k, self.b)))
        yices_assert_formula(self.context, yices_arith_lt_atom(self.e, self.d))

    def print_model(self, model):
        int32_val = c_int32()
        double_val = c_double()

        yices_get_int32_value(model, self.b, int32_val)
        print 'b = {0}'.format(int32_val.value)
        yices_get_int32_value(model, self.t, int32_val)
        print 't = {0}'.format(int32_val.value)
        
        yices_get_double_value(model, self.e, double_val);
        print ("double value of e = {0}".format(double_val.value))



    def solve(self):
        smt_stat = yices_check_context(self.context, None)

        if smt_stat != STATUS_SAT:
               print 'No solution: smt_stat = {0}\n'.format(smt_stat)
        else:
            #print model
            model = yices_get_model(self.context, 1)
            self.print_model(model)
            yices_free_model(model)


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

    solver.solve()
    
    solver.exit()
    print 'bye'
    return 0
    


if __name__ == '__main__':
    sys.exit(main())



