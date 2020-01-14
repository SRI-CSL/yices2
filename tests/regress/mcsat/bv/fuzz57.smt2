(set-logic QF_BV)
(declare-fun _substvar_155_ () (_ BitVec 15))
(declare-fun _substvar_216_ () (_ BitVec 15))
(declare-fun _substvar_258_ () (_ BitVec 15))
(declare-fun _substvar_273_ () (_ BitVec 1))
(assert (let ((e5 (_ bv524 10))) (let ((e7 (bvand _substvar_216_ _substvar_216_))) (let ((e12 (bvmul _substvar_155_ ((_ sign_extend 5) e5)))) (let ((e21 (bvxnor ((_ sign_extend 5) e5) e12))) (let ((e25 (bvlshr ((_ sign_extend 14) _substvar_273_) _substvar_155_))) (let ((e34 (ite (= (_ bv1 1) ((_ extract 3 3) e25)) (_ bv0 15) _substvar_258_))) (let ((e84 (ite (bvsle e21 e34) (_ bv1 1) (_ bv0 1)))) (let ((e251 (bvsle e7 (_ bv0 15)))) (let ((e279 (bvsle (_ bv0 15) _substvar_216_))) (let ((e380 (distinct (_ bv0 1) e84))) (let ((e620 e380)) (let ((e623 (= e620 false))) (let ((e646 (=> e279 e623))) (let ((e692 (ite e646 false true))) (let ((e713 (= e692 true))) (let ((e734 (xor false e251))) (let ((e740 (= e734 e713))) (let ((e748 e740)) (let ((e749 (and e748 e748))) (let ((e751 e749)) (let ((e752 e751)) (let ((e753 e752)) (let ((e754 (and e753 (not (= e7 (_ bv0 15)))))) (let ((e755 (and e754 (not (= e25 (_ bv0 15)))))) (let ((e756 e755)) (let ((e757 e756)) (let ((e758 e757)) (let ((e759 e758)) (let ((e760 (and e759 (not (= _substvar_155_ (_ bv0 15)))))) (let ((e761 e760)) (let ((e762 e761)) (let ((e763 e762)) (let ((e764 e763)) (let ((e765 e764)) (let ((e766 e765)) (let ((e767 e766)) e767)))))))))))))))))))))))))))))))))))))
(check-sat)

