(set-logic QF_BV)
(declare-fun _substvar_56_ () (_ BitVec 9))
(declare-fun _substvar_67_ () (_ BitVec 14))
(declare-fun _substvar_70_ () (_ BitVec 9))
(declare-fun _substvar_75_ () (_ BitVec 9))
(assert (let ((e8 (bvor _substvar_56_ _substvar_75_))) (let ((e9 (bvnor _substvar_56_ _substvar_56_))) (let ((e12 ((_ rotate_right 1) e8))) (let ((e18 (bvuge (_ bv0 9) _substvar_56_))) (let ((e20 (bvule _substvar_75_ _substvar_70_))) (let ((e38 (bvsge (_ bv0 9) e9))) (let ((e59 (bvugt _substvar_67_ (_ bv0 14)))) (let ((e63 (distinct ((_ sign_extend 5) e12) _substvar_67_))) (let ((e64 (and e18 e38))) (let ((e66 (and e63 e20))) (let ((e77 (= e64 true))) (let ((e84 e77)) (let ((e87 (= e66 true))) (let ((e90 (= true e84))) (let ((e98 (xor true e90))) (let ((e101 (= false e59))) (let ((e103 (=> true e98))) (let ((e105 (ite e87 true false))) (let ((e106 (not e103))) (let ((e107 (xor true e101))) (let ((e108 (=> e106 e107))) (let ((e109 (xor e105 e108))) e109)))))))))))))))))))))))
(check-sat)

