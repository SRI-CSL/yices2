(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: intersection-example-simple.proof, node 679178 For more info see: @see "Sarah M. Loos and Andre Platzer. Safe intersections: At the crossing of hybrid systems and verification. In Kyongsu Yi, editor, 14th International IEEE Conference on Intelligent Transportation Systems, ITSC 2011, Washington, DC, USA, Proceedings. 2011."
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun v1 () Real)
(declare-fun A () Real)
(declare-fun B () Real)
(declare-fun v2 () Real)
(declare-fun x1uscore1dollarskuscore561 () Real)
(declare-fun I1 () Real)
(declare-fun t3245uscore0 () Real)
(declare-fun I2 () Real)
(declare-fun x2 () Real)
(declare-fun I2uscore1dollarskuscore821 () Real)
(declare-fun ts3245uscore0 () Real)
(declare-fun x1 () Real)
(declare-fun x2uscore1dollarskuscore587 () Real)
(declare-fun v1uscore1dollarskuscore821 () Real)
(declare-fun xI1 () Real)
(declare-fun V () Real)
(declare-fun xI2 () Real)
(declare-fun ep () Real)
(declare-fun I1uscore1dollarskuscore821 () Real)
(declare-fun v2uscore1dollarskuscore821 () Real)
(assert (not (exists ((ts3245uscore0 Real)) (let ((?v_0 (= I1uscore1dollarskuscore821 2))) (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= v2uscore1dollarskuscore821 0) (= v1uscore1dollarskuscore821 V)) (= xI1 x1uscore1dollarskuscore561)) (= I2uscore1dollarskuscore821 2)) ?v_0) (= I1 2)) (< xI1 x1)) (= I2 2)) (< xI2 x2)) (> B 0)) (>= v1 0)) (<= v1 V)) (>= v2 0)) (<= v2 V)) (>= A 0)) (> V 0)) (> ep 0)) (or (= xI2 x2uscore1dollarskuscore587) (=> (>= t3245uscore0 0) (=> (=> (and (<= 0 ts3245uscore0) (<= ts3245uscore0 t3245uscore0)) (and (and (and (and (>= v1uscore1dollarskuscore821 0) (<= v1uscore1dollarskuscore821 V)) (>= v2uscore1dollarskuscore821 0)) (<= v2uscore1dollarskuscore821 V)) (<= (+ ts3245uscore0 0) ep))) (or ?v_0 (= 0 2))))))))))
(check-sat)
(exit)
