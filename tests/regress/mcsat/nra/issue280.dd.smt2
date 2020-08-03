(set-logic QF_NRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert
  (let (($x123 (<= z 0.0)))
  (let (($x159 (not (<= (* z (* z (- 1.0))) x))))
    (and
      (= (* x x) (+ 1.0 (* y (* y (- 1.0)))))
      (and (<= z 0.0) (not (<= (* z (* z (- 1.0))) x)))))))

(check-sat)
