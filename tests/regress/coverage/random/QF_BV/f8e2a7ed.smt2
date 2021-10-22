(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 9))
(assert (let ((e1(_ bv6 3)))
(let ((e2(_ bv27 6)))
(let ((e3 (! (bvnand ((_ zero_extend 3) e2) v0) :named term3)))
(let ((e4 (! (bvnand e3 v0) :named term4)))
(let ((e5 (! (ite (bvugt v0 e3) (_ bv1 1) (_ bv0 1)) :named term5)))
(let ((e6 (! (bvmul e3 ((_ sign_extend 3) e2)) :named term6)))
(let ((e7 (! (bvnand e4 e3) :named term7)))
(let ((e8 (! ((_ repeat 1) e6) :named term8)))
(let ((e9 (! (bvsrem e6 e8) :named term9)))
(let ((e10 (! (bvurem ((_ zero_extend 8) e5) e8) :named term10)))
(let ((e11 (! (ite (bvsge e2 e2) (_ bv1 1) (_ bv0 1)) :named term11)))
(let ((e12 (! (bvsub e7 e3) :named term12)))
(let ((e13 (! ((_ rotate_right 0) e1) :named term13)))
(let ((e14 (! (bvsgt e9 ((_ zero_extend 8) e5)) :named term14)))
(let ((e15 (! (= e8 e6) :named term15)))
(let ((e16 (! (bvuge e2 ((_ zero_extend 3) e13)) :named term16)))
(let ((e17 (! (bvuge e9 e9) :named term17)))
(let ((e18 (! (bvult v0 ((_ sign_extend 6) e13)) :named term18)))
(let ((e19 (! (bvugt ((_ zero_extend 6) e13) e7) :named term19)))
(let ((e20 (! (= e11 e5) :named term20)))
(let ((e21 (! (bvsge e5 e5) :named term21)))
(let ((e22 (! (bvsle e7 e9) :named term22)))
(let ((e23 (! (bvult v0 ((_ sign_extend 3) e2)) :named term23)))
(let ((e24 (! (distinct e3 ((_ sign_extend 3) e2)) :named term24)))
(let ((e25 (! (bvsle ((_ sign_extend 2) e5) e13) :named term25)))
(let ((e26 (! (bvsle ((_ sign_extend 8) e5) v0) :named term26)))
(let ((e27 (! (bvsle v0 e8) :named term27)))
(let ((e28 (! (= ((_ sign_extend 8) e5) e7) :named term28)))
(let ((e29 (! (bvule e8 ((_ zero_extend 3) e2)) :named term29)))
(let ((e30 (! (= ((_ zero_extend 2) e5) e13) :named term30)))
(let ((e31 (! (= ((_ sign_extend 6) e13) e9) :named term31)))
(let ((e32 (! (bvsge e5 e5) :named term32)))
(let ((e33 (! (= e8 ((_ sign_extend 6) e13)) :named term33)))
(let ((e34 (! (bvuge ((_ sign_extend 3) e2) v0) :named term34)))
(let ((e35 (! (bvsgt e8 ((_ sign_extend 8) e5)) :named term35)))
(let ((e36 (! (distinct e3 e3) :named term36)))
(let ((e37 (! (bvslt ((_ sign_extend 8) e11) e6) :named term37)))
(let ((e38 (! (distinct e6 ((_ sign_extend 6) e1)) :named term38)))
(let ((e39 (! (= ((_ sign_extend 6) e1) e7) :named term39)))
(let ((e40 (! (distinct e6 ((_ zero_extend 6) e1)) :named term40)))
(let ((e41 (! (bvugt e4 e8) :named term41)))
(let ((e42 (! (bvslt ((_ zero_extend 6) e1) e6) :named term42)))
(let ((e43 (! (= e2 ((_ sign_extend 3) e13)) :named term43)))
(let ((e44 (! (bvugt e10 ((_ zero_extend 8) e5)) :named term44)))
(let ((e45 (! (bvuge ((_ zero_extend 6) e13) e12) :named term45)))
(let ((e46 (! (not e38) :named term46)))
(let ((e47 (! (and e45 e31) :named term47)))
(let ((e48 (! (not e29) :named term48)))
(let ((e49 (! (ite e37 e44 e40) :named term49)))
(let ((e50 (! (= e25 e27) :named term50)))
(let ((e51 (! (and e46 e22) :named term51)))
(let ((e52 (! (ite e23 e23 e15) :named term52)))
(let ((e53 (! (xor e20 e19) :named term53)))
(let ((e54 (! (or e48 e41) :named term54)))
(let ((e55 (! (not e33) :named term55)))
(let ((e56 (! (=> e36 e14) :named term56)))
(let ((e57 (! (or e39 e18) :named term57)))
(let ((e58 (! (=> e16 e52) :named term58)))
(let ((e59 (! (xor e34 e32) :named term59)))
(let ((e60 (! (ite e24 e26 e21) :named term60)))
(let ((e61 (! (= e59 e50) :named term61)))
(let ((e62 (! (not e56) :named term62)))
(let ((e63 (! (not e57) :named term63)))
(let ((e64 (! (xor e30 e53) :named term64)))
(let ((e65 (! (=> e17 e64) :named term65)))
(let ((e66 (! (ite e54 e42 e55) :named term66)))
(let ((e67 (! (and e49 e62) :named term67)))
(let ((e68 (! (ite e63 e65 e58) :named term68)))
(let ((e69 (! (and e66 e35) :named term69)))
(let ((e70 (! (xor e69 e67) :named term70)))
(let ((e71 (! (ite e47 e68 e68) :named term71)))
(let ((e72 (! (xor e60 e70) :named term72)))
(let ((e73 (! (= e61 e51) :named term73)))
(let ((e74 (! (xor e73 e43) :named term74)))
(let ((e75 (! (xor e28 e74) :named term75)))
(let ((e76 (! (or e72 e71) :named term76)))
(let ((e77 (! (= e76 e76) :named term77)))
(let ((e78 (! (not e75) :named term78)))
(let ((e79 (! (= e77 e78) :named term79)))
(let ((e80 (! (and e79 (not (= e8 (_ bv0 9)))) :named term80)))
(let ((e81 (! (and e80 (not (= e8 (bvnot (_ bv0 9))))) :named term81)))
e81
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
(get-info :all-statistics)
