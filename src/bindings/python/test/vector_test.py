import unittest
"""
from ..yices import (
    yices_init,
    yices_exit,
    term_vector_t,
    init_term_vector,
    delete_term_vector,
    reset_term_vector,
    type_vector_t,
    init_type_vector,
    delete_type_vector,
    reset_type_vector,
    yval_vector_t,
    init_yval_vector,
    delete_yval_vector,
    reset_yval_vector
    )
"""

from .. import yices as ys

class TestVector(unittest.TestCase):

    def setUp(self):
        ys.yices_init()

    def tearDown(self):
        ys.yices_exit()
        pass

    def test_term_vector(self):
        term_v = ys.term_vector_t()
        ys.init_term_vector(term_v)
        ys.delete_term_vector(term_v)
        ys.reset_term_vector(term_v)

    def test_type_vector(self):
        type_v = ys.type_vector_t()
        ys.init_type_vector(type_v)
        ys.reset_type_vector(type_v)
        ys.delete_type_vector(type_v)
        #yices.type_children(ty, type_v)

    def test_yval_vector(self):
        yval_v = ys.yval_vector_t()
        ys.init_yval_vector(yval_v)
        ys.reset_yval_vector(yval_v)
        ys.delete_yval_vector(yval_v)
