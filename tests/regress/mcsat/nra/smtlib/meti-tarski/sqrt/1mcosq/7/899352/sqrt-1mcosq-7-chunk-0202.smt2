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
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (let ((?v_0 (* skoX 10))) (and (not (<= (* skoX (* skoX (+ (/ 1 2) (* skoX (* skoX (+ (/ (- 1) 24) (* skoX (* skoX (+ (/ 1 720) (* skoX (* skoX (+ (/ (- 1) 40320) (* skoX (* skoX (+ (/ 1 3628800) (* skoX (* skoX (+ (/ (- 1) 479001600) (* skoX (* skoX (+ (/ 1 87178291200) (* skoX (* skoX (+ (/ (- 1) 20922789888000) (* skoX (* skoX (+ (/ 1 6402373705728000) (* skoX (* skoX (+ (/ (- 1) 2432902008176640000) (* skoX (* skoX (/ 1 1124000727777607680000))))))))))))))))))))))))))))))))) 1)) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (and (<= skoY (* pi (/ 1 2))) (and (<= (/ 1 20) skoX) (and (not (<= skoY skoX)) (and (or (not (<= ?v_0 skoY)) (or (not (<= skoY ?v_0)) (<= skoY 0))) (and (<= (* skoY (* skoY (/ (- 1) 2))) (- 1)) (and (<= (* skoY (* skoY (+ (/ (- 1) 2) (* skoY (* skoY (+ (/ 1 24) (* skoY (* skoY (/ (- 1) 720))))))))) (- 1)) (and (<= (* skoY (* skoY (+ (/ (- 1) 2) (* skoY (* skoY (+ (/ 1 24) (* skoY (* skoY (+ (/ (- 1) 720) (* skoY (* skoY (+ (/ 1 40320) (* skoY (* skoY (/ (- 1) 3628800))))))))))))))) (- 1)) (and (<= (* skoY (* skoY (+ (/ 1 2) (* skoY (* skoY (+ (/ (- 1) 24) (* skoY (* skoY (+ (/ 1 720) (* skoY (* skoY (+ (/ (- 1) 40320) (* skoY (* skoY (+ (/ 1 3628800) (* skoY (* skoY (/ (- 1) 479001600)))))))))))))))))) 1) (and (<= (* skoY (* skoY (+ (/ (- 1) 2) (* skoY (* skoY (+ (/ 1 24) (* skoY (* skoY (+ (/ (- 1) 720) (* skoY (* skoY (+ (/ 1 40320) (* skoY (* skoY (+ (/ (- 1) 3628800) (* skoY (* skoY (+ (/ 1 479001600) (* skoY (* skoY (/ (- 1) 87178291200))))))))))))))))))))) (- 1)) (and (<= (* skoY (* skoY (+ (/ 1 2) (* skoY (* skoY (+ (/ (- 1) 24) (* skoY (* skoY (+ (/ 1 720) (* skoY (* skoY (+ (/ (- 1) 40320) (* skoY (* skoY (+ (/ 1 3628800) (* skoY (* skoY (+ (/ (- 1) 479001600) (* skoY (* skoY (+ (/ 1 87178291200) (* skoY (* skoY (/ (- 1) 20922789888000)))))))))))))))))))))))) 1) (and (not (<= (* skoX (* skoX (/ 1 2))) 1)) (and (not (<= (* skoX (* skoX (+ (/ 1 2) (* skoX (* skoX (+ (/ (- 1) 24) (* skoX (* skoX (/ 1 720))))))))) 1)) (and (not (<= (* skoX (* skoX (+ (/ 1 2) (* skoX (* skoX (+ (/ (- 1) 24) (* skoX (* skoX (+ (/ 1 720) (* skoX (* skoX (+ (/ (- 1) 40320) (* skoX (* skoX (/ 1 3628800))))))))))))))) 1)) (not (<= (* skoX (* skoX (+ (/ 1 2) (* skoX (* skoX (+ (/ (- 1) 24) (* skoX (* skoX (+ (/ 1 720) (* skoX (* skoX (+ (/ (- 1) 40320) (* skoX (* skoX (+ (/ 1 3628800) (* skoX (* skoX (+ (/ (- 1) 479001600) (* skoX (* skoX (/ 1 87178291200))))))))))))))))))))) 1))))))))))))))))))))
(check-sat)
(exit)
