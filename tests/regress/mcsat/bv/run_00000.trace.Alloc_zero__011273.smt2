(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun INPUT_10000_0020 () (_ BitVec 8))
(declare-fun INPUT_missed_10000_0020_36468 () (_ BitVec 8))
(assert (let ((?v_0 (bvor (_ bv0 32) (bvand (_ bv16777215 32) (bvor (_ bv0 32) (bvand (_ bv4278255615 32) (concat (_ bv0 16) (bvor (concat (_ bv0 8) (bvand (_ bv255 8) ((_ extract 7 0) (bvxor (_ bv103 32) (bvor (_ bv0 32) (bvand (_ bv16777215 32) (bvor (_ bv0 32) (bvand (_ bv4278255615 32) (bvor (_ bv0 32) (bvand (_ bv4294902015 32) (concat (_ bv0 24) (bvand (_ bv255 8) INPUT_10000_0020)))))))))))) ((_ extract 15 0) (concat (concat (_ bv0 8) (bvand (_ bv255 8) ((_ extract 7 0) (bvadd (_ bv33 32) (bvor (_ bv0 32) (bvand (_ bv16777215 32) (bvor (_ bv0 32) (bvand (_ bv4278255615 32) (bvor (_ bv0 32) (bvand (_ bv4294902015 32) (concat (_ bv0 24) (bvand (_ bv255 8) INPUT_missed_10000_0020_36468)))))))))))) (_ bv0 8))))))))))) (let ((?v_1 (bvor (_ bv0 32) (bvand (_ bv16777215 32) (bvor (_ bv0 32) (bvand (_ bv4278255615 32) (bvor (_ bv0 32) (bvor (_ bv0 32) (bvor (concat (_ bv0 24) ((_ extract 7 0) (bvand (_ bv255 32) ?v_0))) ((_ extract 31 0) (concat (concat (_ bv0 24) ((_ extract 7 0) (concat (_ bv0 8) ((_ extract 31 8) (bvand (_ bv65280 32) ?v_0))))) (_ bv0 8)))))))))))) (and (and (and (and (= (_ bv0 8) ((_ extract 7 0) (bvand (_ bv255 32) ?v_1))) (= (_ bv0 8) ((_ extract 7 0) (concat (_ bv0 8) ((_ extract 31 8) (bvand (_ bv65280 32) ?v_1)))))) (= (_ bv0 8) ((_ extract 7 0) (concat (_ bv0 16) ((_ extract 31 16) (bvand (_ bv16711680 32) ?v_1)))))) (= (_ bv0 8) ((_ extract 7 0) (concat (_ bv0 24) ((_ extract 31 24) (bvand (_ bv4278190080 32) ?v_1)))))) true))))
(check-sat)
(exit)
