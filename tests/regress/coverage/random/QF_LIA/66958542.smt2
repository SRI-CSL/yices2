(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_LIA)
(declare-fun v0 () Int)
(declare-fun v1 () Int)
(assert (let ((e2 5))
(let ((e3 (! (- v0 v1) :named term3)))
(let ((e4 (! (- e3 v1) :named term4)))
(let ((e5 (! (- e3 e4) :named term5)))
(let ((e6 (! (* e2 e3) :named term6)))
(let ((e7 (! (distinct e3 e4) :named term7)))
(let ((e8 (! (< v0 e3) :named term8)))
(let ((e9 (! (= e3 e6) :named term9)))
(let ((e10 (! (>= e6 e3) :named term10)))
(let ((e11 (! (< e3 e5) :named term11)))
(let ((e12 (! (<= e5 v1) :named term12)))
(let ((e13 (! (ite e10 e3 e3) :named term13)))
(let ((e14 (! (ite e12 e6 e13) :named term14)))
(let ((e15 (! (ite e8 e6 e13) :named term15)))
(let ((e16 (! (ite e8 e4 v0) :named term16)))
(let ((e17 (! (ite e9 v1 v0) :named term17)))
(let ((e18 (! (ite e11 e5 e6) :named term18)))
(let ((e19 (! (ite e7 e13 e5) :named term19)))
(let ((e20 (! (> e14 e17) :named term20)))
(let ((e21 (! (< e15 e6) :named term21)))
(let ((e22 (! (= e14 e14) :named term22)))
(let ((e23 (! (>= e16 v1) :named term23)))
(let ((e24 (! (<= e6 e17) :named term24)))
(let ((e25 (! (>= v1 e3) :named term25)))
(let ((e26 (! (> e13 e17) :named term26)))
(let ((e27 (! (< e15 e13) :named term27)))
(let ((e28 (! (> e6 e18) :named term28)))
(let ((e29 (! (= e14 e4) :named term29)))
(let ((e30 (! (>= v0 e4) :named term30)))
(let ((e31 (! (distinct e13 e18) :named term31)))
(let ((e32 (! (>= v0 e14) :named term32)))
(let ((e33 (! (>= e5 e19) :named term33)))
(let ((e34 (! (= e9 e33) :named term34)))
(let ((e35 (! (xor e10 e30) :named term35)))
(let ((e36 (! (= e20 e32) :named term36)))
(let ((e37 (! (= e36 e25) :named term37)))
(let ((e38 (! (ite e35 e31 e23) :named term38)))
(let ((e39 (! (and e22 e29) :named term39)))
(let ((e40 (! (and e24 e24) :named term40)))
(let ((e41 (! (=> e40 e12) :named term41)))
(let ((e42 (! (not e38) :named term42)))
(let ((e43 (! (= e27 e27) :named term43)))
(let ((e44 (! (or e34 e8) :named term44)))
(let ((e45 (! (not e37) :named term45)))
(let ((e46 (! (or e26 e43) :named term46)))
(let ((e47 (! (not e44) :named term47)))
(let ((e48 (! (or e39 e7) :named term48)))
(let ((e49 (! (ite e46 e42 e45) :named term49)))
(let ((e50 (! (xor e49 e28) :named term50)))
(let ((e51 (! (=> e50 e50) :named term51)))
(let ((e52 (! (not e41) :named term52)))
(let ((e53 (! (xor e51 e11) :named term53)))
(let ((e54 (! (= e48 e52) :named term54)))
(let ((e55 (! (= e53 e54) :named term55)))
(let ((e56 (! (xor e55 e55) :named term56)))
(let ((e57 (! (not e21) :named term57)))
(let ((e58 (! (ite e57 e47 e56) :named term58)))
e58
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
(get-value (term3))
(get-value (term4))
(get-value (term5))
(get-value (term6))
(get-value (term7))
(get-value (term8))
(get-value (term9))
(get-value (term10))
(get-value (term11))
(get-value (term12))
(get-value (term13))
(get-value (term14))
(get-value (term15))
(get-value (term16))
(get-value (term17))
(get-value (term18))
(get-value (term19))
(get-value (term20))
(get-value (term21))
(get-value (term22))
(get-value (term23))
(get-value (term24))
(get-value (term25))
(get-value (term26))
(get-value (term27))
(get-value (term28))
(get-value (term29))
(get-value (term30))
(get-value (term31))
(get-value (term32))
(get-value (term33))
(get-value (term34))
(get-value (term35))
(get-value (term36))
(get-value (term37))
(get-value (term38))
(get-value (term39))
(get-value (term40))
(get-value (term41))
(get-value (term42))
(get-value (term43))
(get-value (term44))
(get-value (term45))
(get-value (term46))
(get-value (term47))
(get-value (term48))
(get-value (term49))
(get-value (term50))
(get-value (term51))
(get-value (term52))
(get-value (term53))
(get-value (term54))
(get-value (term55))
(get-value (term56))
(get-value (term57))
(get-value (term58))
(get-info :all-statistics)
