import unittest
from .. import yices

class TestVector(unittest.TestCase):

  def setUp(self):
    yices.init()

  def tearDown(self):
    #yices_exit()
    pass

  def test_term_vector(self):
    term_v = yices.term_vector_t()
    yices.init_term_vector(term_v)
    yices.delete_term_vector(term_v)
    yices.reset_term_vector(term_v)

  def test_type_vector(self):
    type_v = yices.type_vector_t()
    yices.init_type_vector(type_v)
    yices.reset_type_vector(type_v)
    yices.delete_type_vector(type_v)
    #yices.type_children(ty, type_v)

  def test_yval_vector(self):
    yval_v = yices.yval_vector_t()
    yices.init_yval_vector(yval_v)
    yices.reset_yval_vector(yval_v)
    yices.delete_yval_vector(yval_v)
    
