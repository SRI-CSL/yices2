(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_AUFBV)
(declare-fun v0 () (_ BitVec 14))
(declare-fun a1 () (Array  (_ BitVec 4)  (_ BitVec 4)))
(assert (let ((e2(_ bv107 7)))
(let ((e3(_ bv1762 13)))
(let ((e4 (! (bvnor e3 e3) :named term4)))
(let ((e5 (! (ite (bvule ((_ zero_extend 1) e3) v0) (_ bv1 1) (_ bv0 1)) :named term5)))
(let ((e6 (! (ite (bvugt ((_ sign_extend 6) e2) e4) (_ bv1 1) (_ bv0 1)) :named term6)))
(let ((e7 (! (store a1 ((_ extract 5 2) e2) ((_ sign_extend 3) e6)) :named term7)))
(let ((e8 (! (select a1 ((_ zero_extend 3) e5)) :named term8)))
(let ((e9 (! (select e7 ((_ zero_extend 3) e5)) :named term9)))
(let ((e10 (! (select a1 e8) :named term10)))
(let ((e11 (! (select e7 ((_ zero_extend 3) e6)) :named term11)))
(let ((e12 (! (select a1 ((_ extract 8 5) e3)) :named term12)))
(let ((e13 (! (ite (bvuge e10 ((_ zero_extend 3) e5)) (_ bv1 1) (_ bv0 1)) :named term13)))
(let ((e14 (! (ite (= (_ bv1 1) ((_ extract 2 2) e9)) v0 ((_ sign_extend 13) e6)) :named term14)))
(let ((e15 (! (bvshl v0 ((_ sign_extend 1) e3)) :named term15)))
(let ((e16 (! (ite (bvule e4 ((_ sign_extend 9) e12)) (_ bv1 1) (_ bv0 1)) :named term16)))
(let ((e17 (! (bvnot e6) :named term17)))
(let ((e18 (! (ite (bvugt e2 e2) (_ bv1 1) (_ bv0 1)) :named term18)))
(let ((e19 (! (ite (bvsle ((_ sign_extend 10) e8) v0) (_ bv1 1) (_ bv0 1)) :named term19)))
(let ((e20 (! (ite (bvugt ((_ sign_extend 3) e18) e8) (_ bv1 1) (_ bv0 1)) :named term20)))
(let ((e21 (! (ite (= (_ bv1 1) ((_ extract 3 3) e11)) e5 e19) :named term21)))
(let ((e22 (! (bvult ((_ zero_extend 12) e18) e4) :named term22)))
(let ((e23 (! (= e20 e20) :named term23)))
(let ((e24 (! (distinct e10 e8) :named term24)))
(let ((e25 (! (bvule e10 ((_ sign_extend 3) e20)) :named term25)))
(let ((e26 (! (bvsgt ((_ sign_extend 3) e9) e2) :named term26)))
(let ((e27 (! (bvuge ((_ zero_extend 13) e6) v0) :named term27)))
(let ((e28 (! (distinct e10 e12) :named term28)))
(let ((e29 (! (bvuge e8 ((_ sign_extend 3) e21)) :named term29)))
(let ((e30 (! (bvsle e2 ((_ zero_extend 3) e11)) :named term30)))
(let ((e31 (! (bvugt ((_ zero_extend 3) e6) e10) :named term31)))
(let ((e32 (! (bvuge e15 ((_ sign_extend 13) e20)) :named term32)))
(let ((e33 (! (bvslt e10 e12) :named term33)))
(let ((e34 (! (bvuge ((_ sign_extend 9) e8) e4) :named term34)))
(let ((e35 (! (bvslt e10 e12) :named term35)))
(let ((e36 (! (bvsle ((_ sign_extend 3) e17) e11) :named term36)))
(let ((e37 (! (bvslt ((_ sign_extend 13) e13) e15) :named term37)))
(let ((e38 (! (bvule ((_ sign_extend 9) e9) e3) :named term38)))
(let ((e39 (! (distinct ((_ sign_extend 13) e21) e15) :named term39)))
(let ((e40 (! (bvsle ((_ zero_extend 1) e4) e15) :named term40)))
(let ((e41 (! (bvsge e17 e13) :named term41)))
(let ((e42 (! (bvsgt e3 ((_ zero_extend 12) e19)) :named term42)))
(let ((e43 (! (bvsle ((_ zero_extend 12) e6) e3) :named term43)))
(let ((e44 (! (bvsge e18 e5) :named term44)))
(let ((e45 (! (bvule e18 e17) :named term45)))
(let ((e46 (! (distinct ((_ zero_extend 10) e12) e14) :named term46)))
(let ((e47 (! (bvugt ((_ zero_extend 9) e12) e4) :named term47)))
(let ((e48 (! (bvule e12 ((_ sign_extend 3) e6)) :named term48)))
(let ((e49 (! (bvsle e19 e17) :named term49)))
(let ((e50 (! (bvuge ((_ zero_extend 12) e18) e4) :named term50)))
(let ((e51 (! (bvsgt e14 ((_ sign_extend 13) e13)) :named term51)))
(let ((e52 (! (bvsgt ((_ zero_extend 12) e21) e4) :named term52)))
(let ((e53 (! (bvule ((_ sign_extend 12) e16) e4) :named term53)))
(let ((e54 (! (ite e43 e53 e22) :named term54)))
(let ((e55 (! (=> e32 e36) :named term55)))
(let ((e56 (! (or e30 e51) :named term56)))
(let ((e57 (! (xor e56 e23) :named term57)))
(let ((e58 (! (ite e44 e41 e40) :named term58)))
(let ((e59 (! (=> e45 e24) :named term59)))
(let ((e60 (! (= e58 e52) :named term60)))
(let ((e61 (! (xor e59 e25) :named term61)))
(let ((e62 (! (= e33 e38) :named term62)))
(let ((e63 (! (=> e34 e34) :named term63)))
(let ((e64 (! (= e29 e35) :named term64)))
(let ((e65 (! (=> e37 e57) :named term65)))
(let ((e66 (! (or e55 e42) :named term66)))
(let ((e67 (! (=> e27 e31) :named term67)))
(let ((e68 (! (xor e60 e64) :named term68)))
(let ((e69 (! (=> e62 e63) :named term69)))
(let ((e70 (! (and e54 e66) :named term70)))
(let ((e71 (! (=> e68 e69) :named term71)))
(let ((e72 (! (not e48) :named term72)))
(let ((e73 (! (not e26) :named term73)))
(let ((e74 (! (= e28 e73) :named term74)))
(let ((e75 (! (ite e50 e39 e47) :named term75)))
(let ((e76 (! (=> e70 e67) :named term76)))
(let ((e77 (! (and e65 e65) :named term77)))
(let ((e78 (! (= e46 e72) :named term78)))
(let ((e79 (! (and e75 e78) :named term79)))
(let ((e80 (! (=> e61 e74) :named term80)))
(let ((e81 (! (not e76) :named term81)))
(let ((e82 (! (= e71 e77) :named term82)))
(let ((e83 (! (xor e80 e80) :named term83)))
(let ((e84 (! (xor e81 e83) :named term84)))
(let ((e85 (! (ite e49 e84 e84) :named term85)))
(let ((e86 (! (=> e79 e82) :named term86)))
(let ((e87 (! (= e85 e86) :named term87)))
e87
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "NUL")
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
(get-value (term68))
(get-value (term69))
(get-value (term70))
(get-value (term71))
(get-value (term72))
(get-value (term73))
(get-value (term74))
(get-value (term75))
(get-value (term76))
(get-value (term77))
(get-value (term78))
(get-value (term79))
(get-value (term80))
(get-value (term81))
(get-value (term82))
(get-value (term83))
(get-value (term84))
(get-value (term85))
(get-value (term86))
(get-value (term87))
(get-info :all-statistics)
