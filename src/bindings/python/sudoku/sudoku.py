#!/usr/bin/env python


from yices import (yices_init,
                   yices_exit,
                   int_type,
                   int32,
                   term_t,
                   distinct,
                   and2,
                   arith_eq_atom,
                   arith_leq_atom,
                   new_uninterpreted_term,
                   new_config,
                   new_context,
                   assert_formula,
                   check_context,
                   get_model,
                   get_int32_value,
                   free_context,
                   free_config
)


from ctypes import ( c_int32 )


yices_init()

int_t = int_type()

X = [None] * 9

for i in range(9):
    X[i] = [None] * 9
    for j in range(9):
        X[i][j] = new_uninterpreted_term(int_t)



config = new_config()
context = new_context(config)


C = {}
for i in range(1, 10):
    C[i] = int32(i)

one = C[1]
nine = C[9]

def V(i,j):
    return X[i][j]


# x is between 1 and 9
def between_1_and_9(x):
    return and2(arith_leq_atom(one, x), arith_leq_atom(x, nine))

for i in range(9):
    for j in range(9):
        assert_formula(context, between_1_and_9(V(i,j)))




def all_distinct(x):
    n = len(x)
    A = term_t * n
    a = A(*x)
    return distinct(n, a)


# All elements in a row must be distinct
for i in range(9):
    assert_formula(context, all_distinct([V(i,j) for j in range(9)]))  #I.e.  all_distinct(X[i])


# All elements in a column must be distinct
for i in range(9):
    assert_formula(context, all_distinct([V(j,i) for j in range(9)]))

# All elements in each 3x3 square must be distinct
for k in range(3):
    for l in range(3):
        assert_formula(context, all_distinct([V(i + 3 * l, j + 3 * k) for i in range(3) for j in range(3)]))


#initial conditions (part of the UI)
def set_value(context, position, value):
    (row, column) = position
    assert 1 <= row and row <= 9
    assert 1 <= column and column <= 9
    assert 1 <= value and value <= 9
    assert_formula(context, arith_eq_atom(V(row - 1, column - 1), C[value]))


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

smt_stat = check_context(context, None)

if smt_stat != 3:
    print 'No solution: smt_stat = {0}\n'.format(smt_stat)
else:
    model = get_model(context, 1)
    val = c_int32()
    for i in range(9):
        for j in range(9):
            get_int32_value(model, V(i,j), val)
            print 'V({0}, {1}) = {2}\n'.format(i, j, val.value)

#print model

print 'Cleaning up\n'

free_context(context)
free_config(config)


yices_exit()
