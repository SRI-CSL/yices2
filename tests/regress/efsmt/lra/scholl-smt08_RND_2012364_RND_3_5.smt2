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
(assert (and (forall ((?y3 Real)) (or (< (+ (* (- 14) ?y3) (* 49 x1)) 94) (> (+ (* 88 ?y3) (* 83 x1)) 14))) (exists ((?y2 Real)) (forall ((?y3 Real)) (and (not (= (+ (+ (* 31 ?y3) (* (- 96) ?y2)) (* 67 x1)) (- 31))) (= (+ (* 81 ?y3) (* (- 23) ?y2)) (- 21)))))))
(check-sat)
(exit)
