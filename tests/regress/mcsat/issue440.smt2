(set-option :print-success false)
(set-option :produce-models true)
(set-logic QF_UFNIA)
(declare-fun Y () Bool)
(declare-fun X () Bool)
(declare-fun Z () Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert
    (= X
        (=>
            (> (f a) 0)
            (=>
                (= c (mod b 10))
                (=> Y Z)
            )
        )
    )
)
(assert (not X))
(check-sat)
(get-value (X))
