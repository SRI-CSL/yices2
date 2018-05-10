import unittest

from ..yices import *

class TestTypes(unittest.TestCase):

    def setUp(self):
        yices_init()

    def tearDown(self):
        yices_exit()

    def test_types(self):
        bool_t = yices_bool_type()
        int_t = yices_int_type()
        self.assertNotEqual(bool_t, int_t)
        real_t = yices_real_type()
        self.assertNotEqual(real_t, bool_t)
        self.assertNotEqual(real_t, int_t)
        bv_t = yices_bv_type(8)
        scal_t = yices_new_scalar_type(12)
        unint_t = yices_new_uninterpreted_type()
        tup1_t = yices_tuple_type1(bool_t)
        tup2_t = yices_tuple_type2(int_t, real_t)
        tup3_t = yices_tuple_type3(bv_t, scal_t, unint_t)
        ta4 = make_type_array([bool_t, tup1_t, tup2_t, tup3_t])
        tup4_t = yices_tuple_type(4, ta4)
        fun1_t = yices_function_type1(int_t, bool_t)
        fun2_t = yices_function_type2(real_t, bv_t, scal_t)
        fun3_t = yices_function_type3(tup1_t, tup2_t, tup3_t, fun1_t)
        fun4_t = yices_function_type(4, ta4, fun3_t)

        self.assertTrue(yices_type_is_bool(bool_t))
        self.assertFalse(yices_type_is_bool(int_t))
        self.assertTrue(yices_type_is_int(int_t))
        self.assertTrue(yices_type_is_real(real_t))
        self.assertTrue(yices_type_is_arithmetic(real_t))
        self.assertTrue(yices_type_is_bitvector(bv_t))
        self.assertTrue(yices_type_is_tuple(tup1_t))
        self.assertTrue(yices_type_is_function(fun4_t))
        self.assertTrue(yices_type_is_scalar(scal_t))
        self.assertTrue(yices_type_is_uninterpreted(unint_t))
        self.assertTrue(yices_test_subtype(int_t, real_t))
        self.assertFalse(yices_test_subtype(real_t, int_t))
        self.assertEqual(yices_bvtype_size(bv_t), 8)
        self.assertEqual(yices_scalar_type_card(scal_t), 12)
        self.assertEqual(yices_type_num_children(tup3_t), 3)
        self.assertEqual(yices_type_child(tup3_t, 1), scal_t)
        type_v = type_vector_t()
        yices_init_type_vector(type_v)
        yices_type_children(tup4_t, type_v)
        self.assertEqual(type_v.size, 4)
        self.assertEqual(type_v.data[0], bool_t)
        self.assertEqual(type_v.data[1], tup1_t)
        self.assertEqual(type_v.data[2], tup2_t)
        self.assertEqual(type_v.data[3], tup3_t)
