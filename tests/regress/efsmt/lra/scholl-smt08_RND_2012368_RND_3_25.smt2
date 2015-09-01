(set-logic LRA)
(set-info :source |
   Scholl, Christoph; Disch, Stefan; Pigorsch, Florian and Kupferschmid, 
   Stefan; Using an SMT Solver and Craig Interpolation to Detect and Remove 
   Redundant Linear Constraints in Representations of Non-Convex Polyhedra.
   Proceedings of 6th International Workshop on Satisfiability Modulo
   Theories, Princeton, USA, July 2008.
   <http://abs.informatik.uni-freiburg.de/smtbench/>
|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unsat)
(declare-fun y3 () Real)
(declare-fun x1 () Real)
(declare-fun y2 () Real)
(assert (and (forall ((?y3 Real)) (let ((?v_0 (* (- 42) x1))) (or (and (or (and (and (< (* (- 33) x1) 94) (> (* (- 73) ?y3) (- 64))) (not (= (+ (* 75 ?y3) (* 94 x1)) 87))) (and (or (< (* 8 ?y3) 49) (<= (+ (* 93 ?y3) (* (- 19) x1)) (- 12))) (and (not (= (* (- 78) x1) 68)) (<= (+ (* 2 ?y3) (* (- 58) x1)) 0)))) (or (or (or (>= (* (- 44) x1) (- 14)) (<= (+ (* (- 23) ?y3) (* (- 64) x1)) 0)) (and (< (* 73 ?y3) (- 2)) (> (* (- 43) x1) 77))) (or (and (= (+ (* (- 48) ?y3) (* 82 x1)) (- 63)) (= (* 78 x1) 42)) (>= (* (- 36) ?y3) (- 5))))) (and (or (or (<= (+ (* (- 35) ?y3) (* 93 x1)) 14) (< (* 50 x1) (- 35))) (and (<= (* 99 ?y3) 83) (< (+ (* (- 1) ?y3) (* (- 81) x1)) 0))) (or (and (< (* (- 39) x1) 88) (< (+ (* (- 9) ?y3) (* (- 17) x1)) 73)) (or (and (>= (* (- 30) ?y3) 0) (< (+ (* 95 ?y3) (* (- 88) x1)) (- 80))) (or (>= ?v_0 0) (<= ?v_0 0)))))))) (exists ((?y2 Real)) (forall ((?y3 Real)) (let ((?v_1 (* 68 x1)) (?v_3 (* 33 ?y2)) (?v_4 (* 55 ?y3)) (?v_2 (* (- 59) ?y3))) (and (or (or (not (= (+ (+ (* (- 55) ?y3) (* (- 95) ?y2)) ?v_1) (- 31))) (= (+ (* (- 70) ?y3) (* (- 96) ?y2)) (- 96))) (or (or (or (< (* (- 75) ?y3) 31) (> (+ (* (- 86) ?y3) ?v_1) (- 58))) (or (= (+ (+ ?v_2 (* 30 ?y2)) (* (- 16) x1)) 6) (<= (+ (+ (* 58 ?y3) (* (- 85) ?y2)) (* (- 58) x1)) 0))) (or (or (>= (+ (* 85 ?y2) (* (- 34) x1)) 67) (not (= (* (- 36) ?y2) 0))) (or (< (+ (* (- 30) ?y3) (* 37 x1)) (- 26)) (< (+ (* 5 ?y3) (* 55 x1)) 97))))) (and (and (and (or (= (+ (+ (* 25 ?y3) ?v_3) (* 82 x1)) (- 21)) (> (* 21 ?y3) 32)) (or (<= (+ (* (- 13) ?y3) (* (- 84) ?y2)) (- 54)) (>= (+ (+ (* (- 3) ?y3) (* (- 72) ?y2)) (* (- 82) x1)) 40))) (or (< (+ (+ (* 66 ?y3) (* 14 ?y2)) (* (- 24) x1)) (- 23)) (<= (+ (* (- 56) ?y3) (* (- 26) x1)) 44))) (and (or (not (= (+ (* (- 34) ?y2) (* (- 69) x1)) 81)) (not (= (+ (+ (* (- 76) ?y3) (* 51 ?y2)) (* 54 x1)) 63))) (and (and (>= (+ (+ (* (- 64) ?y3) (* 68 ?y2)) (* 51 x1)) 0) (> (+ (+ ?v_4 (* (- 8) ?y2)) (* (- 59) x1)) 2)) (or (< (+ (+ ?v_2 ?v_3) (* (- 20) x1)) (- 20)) (< (+ (+ ?v_4 (* (- 11) ?y2)) (* 49 x1)) 28)))))))))))
(check-sat)
(exit)
