import unittest
from .. import yices
from ctypes import *

class TestContext(unittest.TestCase):

  def setUp(self):
    yices.init()

  def tearDown(self):
    pass

  def test_config(self):
    cfg = yices.new_config()
    # Valid call
    yices.set_config(cfg, "mode", "push-pop")
    # Invalid name
    with self.assertRaisesRegexp(yices.YicesException, 'invalid parameter'):
      yices.set_config(cfg, "baz", "bar")
    # err = yices.error_code()
    # self.assertEqual(err, 501L)
    # Invalid value
    with self.assertRaisesRegexp(yices.YicesException, 'value not valid for parameter'):
      yices.set_config(cfg, "mode", "bar")
    # err = yices.error_code()
    # self.assertEqual(err, 502L)
    yices.default_config_for_logic(cfg, "QF_UFNIRA")
    yices.free_config(cfg)

  def test_context(self):
    cfg = yices.new_config()
    ctx = yices.new_context(cfg)
    stat = yices.context_status(ctx)
    ret = yices.push(ctx)
    ret = yices.pop(ctx)
    yices.reset_context(ctx)
    ret = yices.context_enable_option(ctx, "arith-elim")
    ret = yices.context_disable_option(ctx, "arith-elim")
    stat = yices.context_status(ctx)
    self.assertEqual(stat, 0)
    yices.reset_context(ctx)
    bool_t = yices.bool_type()
    bvar1 = yices.new_variable(bool_t)
    with self.assertRaisesRegexp(yices.YicesException, 'assertion contains a free variable'):
      yices.assert_formula(ctx, bvar1)
    bv_t = yices.bv_type(3)
    bvvar1 = yices.new_uninterpreted_term(bv_t)
    yices.set_term_name(bvvar1, 'x')
    bvvar2 = yices.new_uninterpreted_term(bv_t)
    yices.set_term_name(bvvar2, 'y')
    bvvar3 = yices.new_uninterpreted_term(bv_t)
    yices.set_term_name(bvvar3, 'z')
    fmla1 = yices.parse_term('(= x (bv-add y z))')
    fmla2 = yices.parse_term('(bv-gt y 0b000)')
    fmla3 = yices.parse_term('(bv-gt z 0b000)')
    yices.assert_formula(ctx, fmla1)
    yices.assert_formulas(ctx, 3, (yices.term_t * 3)(fmla1, fmla2, fmla3))
    smt_stat = yices.check_context(ctx, None)
    self.assertEqual(smt_stat, 3) # STATUS_SAT
    yices.assert_blocking_clause(ctx)
    yices.stop_search(ctx)
    param = yices.new_param_record()
    yices.default_params_for_context(ctx, param)
    yices.set_param(param, "dyn-ack", "true")
    with self.assertRaisesRegexp(yices.YicesException, 'invalid parameter'):
      yices.set_param(param, "foo", "bar")
    with self.assertRaisesRegexp(yices.YicesException, 'value not valid for parameter'):
      yices.set_param(param, "dyn-ack", "bar")
    yices.free_param_record(param)
    yices.free_context(ctx)


if __name__ == '__main__':
  unittest.main()
