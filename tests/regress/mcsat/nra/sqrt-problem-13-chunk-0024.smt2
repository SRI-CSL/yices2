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
(set-info :status sat)
(declare-fun skoSXY () Real)
(declare-fun skoT () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (= (+ (* skoSXY (- 1)) (* skoT (* skoT skoSXY))) skoX)) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1))) skoY) (and (<= skoY (/ 33 32)) (and (<= skoX 2) (and (<= (/ 3 2) skoX) (and (<= 1 skoY) (and (<= 0 skoT) (<= 0 skoSXY)))))))))
(check-sat)
(exit)
