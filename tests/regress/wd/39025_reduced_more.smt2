(set-logic QF_UFIDL)
; benchmark generated from python API
(set-info :status unknown)
(declare-fun t.curr () Int)
(declare-fun t.l () Int)
(declare-fun NULL () Int)
(declare-fun t.nxt (Int) Int)
(declare-fun i2 () Int)
(declare-fun t.suc () Int)
(declare-fun t.H_nxt (Int) Bool)

(assert (= (t.nxt t.suc) t.suc))

(assert (not (= (t.nxt t.curr) t.curr)))

(assert (t.H_nxt (t.nxt t.curr)))

(assert (not (t.H_nxt t.curr)))

(assert (or (= i2 t.suc) (= i2 NULL)))

(assert (or (= (t.nxt t.suc) t.curr) (= (t.nxt t.suc) NULL)))

(assert (or (not (= (t.nxt t.l) t.l)) (not (= (t.nxt t.curr) t.suc))))

(check-sat)
