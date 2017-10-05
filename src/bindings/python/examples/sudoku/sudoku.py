#!/usr/bin/env python

from yices import *

from ctypes import ( c_int32 )

yices_init()


int_t = yices_int_type()


#seems logical to make the terms in a grid.
X = [None] * 9
for i in range(9):
    X[i] = [None] * 9
    for j in range(9):
        X[i][j] = yices_new_uninterpreted_term(int_t)

#not real happy about the indexing going from 0 to 8, but
#isolating access via V could make it easier to go from 1 to 9
def V(i,j):
    return X[i][j]



#make the constants that we will need
C = {}
for i in range(1, 10):
    C[i] = yices_int32(i)

one = C[1]
nine = C[9]


config = yices_new_config()
yices_default_config_for_logic(config, "QF_LIA")
context = yices_new_context(config)



# x is between 1 and 9
def between_1_and_9(x):
    return yices_and2(yices_arith_leq_atom(one, x), yices_arith_leq_atom(x, nine))

for i in range(9):
    for j in range(9):
        yices_assert_formula(context, between_1_and_9(V(i,j)))


def all_distinct(x):
    n = len(x)
    a = make_term_array(x)
    return yices_distinct(n, a)

# All elements in a row must be distinct
for i in range(9):
    yices_assert_formula(context, all_distinct([V(i,j) for j in range(9)]))  #I.e.  all_distinct(X[i])


# All elements in a column must be distinct
for i in range(9):
    yices_assert_formula(context, all_distinct([V(j,i) for j in range(9)]))

# All elements in each 3x3 square must be distinct
for k in range(3):
    for l in range(3):
        yices_assert_formula(context, all_distinct([V(i + 3 * l, j + 3 * k) for i in range(3) for j in range(3)]))


#initial conditions (part of the UI)
def set_value(context, position, value):
    (row, column) = position
    assert 1 <= row and row <= 9
    assert 1 <= column and column <= 9
    assert 1 <= value and value <= 9
    yices_assert_formula(context, yices_arith_eq_atom(V(row - 1, column - 1), C[value]))


#
# Constraints:
#
#   -------------------------
#   |     2 |       | 7 6 8 |
#   | 4   7 |       | 5     |
#   |       | 8   7 |       |
#   -------------------------
#   |   5   |   1   |       |
#   |   2 8 |       | 4     |
#   | 3     |   4   |   7   |
#   -------------------------
#   |       | 3   1 |       |
#   |     9 |       | 8   5 |
#   | 6 7 1 |       | 2     |
#   -------------------------
#

set_value(context, (1, 3), 2)
set_value(context, (1, 7), 7)
set_value(context, (1, 8), 6)
set_value(context, (1, 9), 8)

set_value(context, (2, 1), 4)
set_value(context, (2, 3), 7)
set_value(context, (2, 7), 5)

set_value(context, (3, 4), 8)
set_value(context, (3, 6), 7)

set_value(context, (4, 2), 5)
set_value(context, (4, 5), 1)

set_value(context, (5, 2), 2)
set_value(context, (5, 3), 8)
set_value(context, (5, 7), 4)

set_value(context, (6, 1), 3)
set_value(context, (6, 5), 4)
set_value(context, (6, 8), 7)

set_value(context, (7, 4), 3)
set_value(context, (7, 6), 1)

set_value(context, (8, 3), 9)
set_value(context, (8, 7), 8)
set_value(context, (8, 9), 5)

set_value(context, (9, 1), 6)
set_value(context, (9, 2), 7)
set_value(context, (9, 3), 1)
set_value(context, (9, 7), 2)

#check sat

smt_stat = yices_check_context(context, None)

if smt_stat != STATUS_SAT:
    print 'No solution: smt_stat = {0}\n'.format(smt_stat)
else:
    #print model
    model = yices_get_model(context, 1)
    val = c_int32()
    for i in range(9):
        for j in range(9):
            yices_get_int32_value(model, V(i,j), val)
            print 'V({0}, {1}) = {2}'.format(i, j, val.value)
    yices_free_model(model)

print 'Cleaning up\n'

yices_free_context(context)
yices_free_config(config)


yices_exit()
