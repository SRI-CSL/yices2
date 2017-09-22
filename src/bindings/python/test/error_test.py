import unittest
from .. import yices



class TestError(unittest.TestCase):

    def setUp(self):
        yices.yices_init()

    def tearDown(self):
        #yices.exit()
        pass

    def test_error(self):
        # Simple yices.reset test causes segmentation fault on Linux
        #yices.reset()

        # First with no error
        errcode = yices.error_code()
        self.assertEqual(errcode, 0L)
        errep = yices.error_report()
        self.assertEqual(errep.code, 0L)
        yices.clear_error()
        errstr = yices.error_string()
        self.assertEqual(errstr, 'no error')
        yices.print_error_fd(1)

        # Illegal - only scalar or uninterpreted types allowed
        bool_t = yices.bool_type()
        self.assertTrue(yices.type_is_bool(bool_t))
        with self.assertRaisesRegexp(yices.YicesException, 'invalid type in constant creation'):
            const1 = yices.constant(bool_t, 0)
        errpt = yices.error_report()
        self.assertEqual(yices.error_code(), 0)
        self.assertEqual(yices.error_code(), errpt.code)
        errstr = yices.error_string()
        self.assertEqual(errstr, 'no error')
        yices.print_error_fd(1)
        yices.clear_error()
        self.assertEqual(yices.error_code(), 0L)
