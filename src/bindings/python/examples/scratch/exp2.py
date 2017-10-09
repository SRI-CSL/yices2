#!/usr/bin/env python

"""

In this example we use the iterative constraint solver suggested  by BD:

    Let x be a vector of integer and real variables. Suppose we want to
    solve a set of constraints C[x] while minimizing the value of F[x].
    
    One simple strategy is to first find an initial solution x0 to C:

    C[x0]

    then iteratively find x1, x2, x3, x4 ....

    such that

    C[x{n+1}]  and F(x{n+1}) < F(xn) - delta

    for some suitable delta.

In the example we do here 

    C is the conjuction of 
     -  b is in bit_range (2, 3, 4, 5, 6, 7, 8)
     -  t is in time_range (10, 20, 30, 40)
     -  e * t = k * b,   where k comes in from the command line
     -  e < d,   where d comes in from the command line


"""



import sys

from ylib import *

from solver import Solver
            


def make_C(b, t, e, k, d):
    """ Construct the boolean constraint C.
    
     C is the conjuction of 
    
     b is in bit_range
     t is in time_range
     e * t = k * b
     e < d
    """
    BITRANGE = (2, 3, 4, 5, 6, 7, 8)
    TRANGE = (10, 20, 30, 40)
    brange = [ yices_int32(i) for i in BITRANGE ]
    trange = [ yices_int32(i) for i in TRANGE ]
    
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

    return C

    
def make_F(b, t, e, k, d):
    """Construct F the real valued term we want to minimize.

      F is the sum of:
    
      100 * t
      144 / b
      e
    
    This is designed so that we want to make t as small as possible, 
    then make b as small as possible, finally using e to break any ties.

    Other measures are certainly possible, for example we may want to
    maximize b above all, so the term would have to be adjusted so 
    that the b term dominated.

    """
    f = make_empty_term_array(3)

    f[0] = yices_mul(yices_int32(100), t)
    f[1] = yices_division(yices_int32(144), b)
    f[2] = e

    F = yices_sum(3, f)
    return F




def main():

    (ok, pk, pd) = parse_k_and_d()

    if not ok:
        print 'Try, for example, ./exp2.py 2 0.4'
        return 1

    yices_init()

    #Need to make C, F, and delta.

    k =  yices_parse_float(pk)
    d =  yices_parse_float(pd)

    #name the types we need 
    int_t = yices_int_type()
    real_t = yices_real_type()
        
    #just make e, b and t for now
    b =  declare_var('b', int_t)
    t =  declare_var('t', int_t)
    e =  declare_var('e', real_t)

    # construct the constraint set as a boolean term
    C = make_C(b, t, e, k, d)

    # construct the measure we want to minimize
    F = make_F(b, t, e, k, d)



    solver = Solver(C, F, d)

    
    solution = solver.iterate()


    if solution is not None:
        yices_free_model(solution)
    
    yices_exit()

 
    return 0


if __name__ == '__main__':
    sys.exit(main())
    

        
