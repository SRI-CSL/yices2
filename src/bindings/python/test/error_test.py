import unittest

from ..yices import *



class TestError(unittest.TestCase):

    def setUp(self):
        yices_init()

    def tearDown(self):
        yices_exit()

    def test_error(self):
        # Simple yices_reset test causes segmentation fault on Linux
        #yices_reset()

        # First with no error
        errcode = yices_error_code()
        self.assertEqual(errcode, 0L)
        errep = yices_error_report()
        self.assertEqual(errep.code, 0L)
        yices_clear_error()
        errstr = yices_error_string()
        self.assertEqual(errstr, 'no error')
        yices_print_error_fd(1)

        # Illegal - only scalar or uninterpreted types allowed
        bool_t = yices_bool_type()
        self.assertTrue(yices_type_is_bool(bool_t))
        with self.assertRaisesRegexp(YicesException, 'invalid type in constant creation'):
            const1 = yices_constant(bool_t, 0)
        errpt = yices_error_report()
        self.assertEqual(yices_error_code(), 0)
        self.assertEqual(yices_error_code(), errpt.code)
        errstr = yices_error_string()
        self.assertEqual(errstr, 'no error')
        yices_print_error_fd(1)
        yices_clear_error()
        self.assertEqual(yices_error_code(), 0L)
