import unittest


from ..yices import (
    yices_init,
    yices_exit,
    term_vector_t,
    yices_init_term_vector,
    yices_delete_term_vector,
    yices_reset_term_vector,
    type_vector_t,
    yices_init_type_vector,
    yices_delete_type_vector,
    yices_reset_type_vector,
    yval_vector_t,
    yices_init_yval_vector,
    yices_delete_yval_vector,
    yices_reset_yval_vector
    )


# MYSTERY:
#
# from ..yices import *
#
# causes the  error:
#
# E       TypeError: test_subtype() takes exactly 2 arguments (0 given)
#

class TestVector(unittest.TestCase):

    def setUp(self):
        yices_init()

    def tearDown(self):
        yices_exit()
        pass

    def test_term_vector(self):
        term_v = term_vector_t()
        yices_init_term_vector(term_v)
        yices_delete_term_vector(term_v)
        yices_reset_term_vector(term_v)

    def test_type_vector(self):
        type_v = type_vector_t()
        yices_init_type_vector(type_v)
        yices_reset_type_vector(type_v)
        yices_delete_type_vector(type_v)
        #yices_type_children(ty, type_v)

    def test_yval_vector(self):
        yval_v = yval_vector_t()
        yices_init_yval_vector(yval_v)
        yices_reset_yval_vector(yval_v)
        yices_delete_yval_vector(yval_v)
