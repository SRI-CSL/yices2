import unittest

from ..yices import *


class TestContext(unittest.TestCase):

    def setUp(self):
        yices_init()

    def tearDown(self):
        yices_exit()

    def test_config(self):
        cfg = yices_new_config()
        # Valid call
        yices_set_config(cfg, "mode", "push-pop")
        # Invalid name
        with self.assertRaisesRegexp(YicesException, 'invalid parameter'):
            yices_set_config(cfg, "baz", "bar")
        # err = yices_error_code()
        # self.assertEqual(err, 501L)
        # Invalid value
        with self.assertRaisesRegexp(YicesException, 'value not valid for parameter'):
            yices_set_config(cfg, "mode", "bar")
        # err = yices_error_code()
        # self.assertEqual(err, 502L)
        yices_default_config_for_logic(cfg, "QF_UFNIRA")
        yices_free_config(cfg)

    def test_context(self):
        cfg = yices_new_config()
        ctx = yices_new_context(cfg)
        stat = yices_context_status(ctx)
        ret = yices_push(ctx)
        ret = yices_pop(ctx)
        yices_reset_context(ctx)
        ret = yices_context_enable_option(ctx, "arith-elim")
        ret = yices_context_disable_option(ctx, "arith-elim")
        stat = yices_context_status(ctx)
        self.assertEqual(stat, 0)
        yices_reset_context(ctx)
        bool_t = yices_bool_type()
        bvar1 = yices_new_variable(bool_t)
        with self.assertRaisesRegexp(YicesException, 'assertion contains a free variable'):
            yices_assert_formula(ctx, bvar1)
        bv_t = yices_bv_type(3)
        bvvar1 = yices_new_uninterpreted_term(bv_t)
        yices_set_term_name(bvvar1, 'x')
        bvvar2 = yices_new_uninterpreted_term(bv_t)
        yices_set_term_name(bvvar2, 'y')
        bvvar3 = yices_new_uninterpreted_term(bv_t)
        yices_set_term_name(bvvar3, 'z')
        fmla1 = yices_parse_term('(= x (bv-add y z))')
        fmla2 = yices_parse_term('(bv-gt y 0b000)')
        fmla3 = yices_parse_term('(bv-gt z 0b000)')
        yices_assert_formula(ctx, fmla1)
        yices_assert_formulas(ctx, 3, make_term_array([fmla1, fmla2, fmla3]))
        smt_stat = yices_check_context(ctx, None)
        self.assertEqual(smt_stat, 3) # STATUS_SAT
        yices_assert_blocking_clause(ctx)
        yices_stop_search(ctx)
        param = yices_new_param_record()
        yices_default_params_for_context(ctx, param)
        yices_set_param(param, "dyn-ack", "true")
        with self.assertRaisesRegexp(YicesException, 'invalid parameter'):
            yices_set_param(param, "foo", "bar")
        with self.assertRaisesRegexp(YicesException, 'value not valid for parameter'):
            yices_set_param(param, "dyn-ack", "bar")
        yices_free_param_record(param)
        yices_free_context(ctx)


if __name__ == '__main__':
    unittest.main()
