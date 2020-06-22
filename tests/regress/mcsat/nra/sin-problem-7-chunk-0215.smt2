(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (let ((?v_0 (* skoX (/ (- 1) 6))) (?v_1 (* skoX (/ 1 120))) (?v_2 (* skoX (/ (- 1) 5040)))) (and (<= skoY 0) (and (not (<= (* skoY (+ (* skoX (* skoX (+ (/ 1 6) (* skoX (* skoX (+ (/ (- 1) 120) (* skoX (* skoX (+ (/ 1 5040) (* skoX (* skoX (+ (/ (- 1) 362880) (* skoX (* skoX (/ 1 39916800))))))))))))))) (* skoY (* skoY (/ (- 1) 6))))) 0)) (and (not (<= (* skoY (* skoY (+ ?v_0 (* skoY (* skoY (+ ?v_1 (* skoY (* skoY (+ ?v_2 (* skoY (* skoY (* skoX (/ 1 362880))))))))))))) (* skoX (* skoX (* skoX (+ (/ (- 1) 6) (* skoX (* skoX (+ (/ 1 120) (* skoX (* skoX (+ (/ (- 1) 5040) (* skoX (* skoX (+ (/ 1 362880) (* skoX (* skoX (/ (- 1) 39916800)))))))))))))))))) (and (not (<= (* skoY (+ (* skoX (* skoX (+ (/ 1 6) (* skoX (* skoX (+ (/ (- 1) 120) (* skoX (* skoX (/ 1 5040))))))))) (* skoY (* skoY (+ (/ (- 1) 6) (* skoY (* skoY (+ (/ 1 120) (* skoY (* skoY (+ (/ (- 1) 5040) (* skoY (* skoY (/ 1 362880)))))))))))))) 0)) (and (not (<= (* skoY (* skoY (+ ?v_0 (* skoY (* skoY ?v_1))))) (* skoX (* skoX (* skoX (+ (/ (- 1) 6) (* skoX (* skoX (+ (/ 1 120) (* skoX ?v_2)))))))))) (and (not (<= (* skoY (+ (* skoX (* skoX (/ 1 6))) (* skoY (* skoY (+ (/ (- 1) 6) (* skoY (* skoY (/ 1 120)))))))) 0)) (and (not (<= skoX 0)) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (and (<= skoY (* pi (/ 1 2))) (and (<= 0 skoX) (not (<= skoY skoX)))))))))))))))
(check-sat)
(exit)
