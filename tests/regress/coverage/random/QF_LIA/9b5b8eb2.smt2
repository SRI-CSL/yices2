(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_LIA)
(declare-fun v0 () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(assert (let ((e3 7))
(let ((e4 (! (+ v2 v0) :named term4)))
(let ((e5 (! (* v0 e3) :named term5)))
(let ((e6 (! (+ v1 v2) :named term6)))
(let ((e7 (! (> v1 v2) :named term7)))
(let ((e8 (! (distinct e6 v2) :named term8)))
(let ((e9 (! (<= e4 v1) :named term9)))
(let ((e10 (! (>= e5 e5) :named term10)))
(let ((e11 (! (> e4 e4) :named term11)))
(let ((e12 (! (> v1 e5) :named term12)))
(let ((e13 (! (= e5 v0) :named term13)))
(let ((e14 (! (ite e9 v0 e5) :named term14)))
(let ((e15 (! (ite e12 e6 v0) :named term15)))
(let ((e16 (! (ite e7 v2 e5) :named term16)))
(let ((e17 (! (ite e12 v1 v2) :named term17)))
(let ((e18 (! (ite e10 v1 e17) :named term18)))
(let ((e19 (! (ite e13 e4 v1) :named term19)))
(let ((e20 (! (ite e11 e4 v2) :named term20)))
(let ((e21 (! (ite e9 e15 e6) :named term21)))
(let ((e22 (! (ite e8 e14 e19) :named term22)))
(let ((e23 (! (= e5 e15) :named term23)))
(let ((e24 (! (>= v2 e22) :named term24)))
(let ((e25 (! (>= e14 e4) :named term25)))
(let ((e26 (! (<= e18 e20) :named term26)))
(let ((e27 (! (> e17 e16) :named term27)))
(let ((e28 (! (= e18 v1) :named term28)))
(let ((e29 (! (= e19 v0) :named term29)))
(let ((e30 (! (distinct e15 e15) :named term30)))
(let ((e31 (! (= e18 e17) :named term31)))
(let ((e32 (! (distinct v2 e4) :named term32)))
(let ((e33 (! (distinct e17 e6) :named term33)))
(let ((e34 (! (> e20 e19) :named term34)))
(let ((e35 (! (<= v0 e5) :named term35)))
(let ((e36 (! (< v0 e4) :named term36)))
(let ((e37 (! (>= v1 e21) :named term37)))
(let ((e38 (! (or e24 e25) :named term38)))
(let ((e39 (! (and e36 e27) :named term39)))
(let ((e40 (! (and e29 e37) :named term40)))
(let ((e41 (! (=> e9 e23) :named term41)))
(let ((e42 (! (and e39 e28) :named term42)))
(let ((e43 (! (xor e40 e13) :named term43)))
(let ((e44 (! (= e12 e7) :named term44)))
(let ((e45 (! (= e42 e42) :named term45)))
(let ((e46 (! (=> e32 e11) :named term46)))
(let ((e47 (! (xor e38 e8) :named term47)))
(let ((e48 (! (=> e30 e30) :named term48)))
(let ((e49 (! (= e47 e47) :named term49)))
(let ((e50 (! (xor e34 e35) :named term50)))
(let ((e51 (! (and e46 e10) :named term51)))
(let ((e52 (! (=> e26 e43) :named term52)))
(let ((e53 (! (not e51) :named term53)))
(let ((e54 (! (not e50) :named term54)))
(let ((e55 (! (or e41 e49) :named term55)))
(let ((e56 (! (not e54) :named term56)))
(let ((e57 (! (not e44) :named term57)))
(let ((e58 (! (xor e33 e55) :named term58)))
(let ((e59 (! (and e58 e57) :named term59)))
(let ((e60 (! (and e53 e53) :named term60)))
(let ((e61 (! (and e48 e60) :named term61)))
(let ((e62 (! (and e31 e45) :named term62)))
(let ((e63 (! (xor e59 e62) :named term63)))
(let ((e64 (! (not e56) :named term64)))
(let ((e65 (! (and e61 e64) :named term65)))
(let ((e66 (! (and e65 e63) :named term66)))
(let ((e67 (! (xor e66 e52) :named term67)))
e67
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "/dev/null")
(get-model)
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
(get-value (term59))
(get-value (term60))
(get-value (term61))
(get-value (term62))
(get-value (term63))
(get-value (term64))
(get-value (term65))
(get-value (term66))
(get-value (term67))
(get-info :all-statistics)