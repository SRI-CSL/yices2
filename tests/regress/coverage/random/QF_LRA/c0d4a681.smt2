(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_LRA)
(declare-fun v0 () Real)
(assert (let ((e1 2))
(let ((e2 (! 14 :named term2)))
(let ((e3 (! (* (- e2) v0) :named term3)))
(let ((e4 (! (- e3 e3) :named term4)))
(let ((e5 (! (+ e4 e4) :named term5)))
(let ((e6 (! (* e5 e1) :named term6)))
(let ((e7 (! (<= e6 v0) :named term7)))
(let ((e8 (! (>= e3 e5) :named term8)))
(let ((e9 (! (= e6 e5) :named term9)))
(let ((e10 (! (distinct e4 e5) :named term10)))
(let ((e11 (! (ite e10 v0 e6) :named term11)))
(let ((e12 (! (ite e7 e4 e4) :named term12)))
(let ((e13 (! (ite e8 e3 e3) :named term13)))
(let ((e14 (! (ite e7 e11 e6) :named term14)))
(let ((e15 (! (ite e9 e12 v0) :named term15)))
(let ((e16 (! (ite e7 e11 e12) :named term16)))
(let ((e17 (! (ite e7 e5 e15) :named term17)))
(let ((e18 (! (<= e16 e12) :named term18)))
(let ((e19 (! (< e3 e12) :named term19)))
(let ((e20 (! (= e12 e17) :named term20)))
(let ((e21 (! (distinct v0 e16) :named term21)))
(let ((e22 (! (>= e12 e14) :named term22)))
(let ((e23 (! (= e11 e4) :named term23)))
(let ((e24 (! (<= e5 e6) :named term24)))
(let ((e25 (! (= e5 e4) :named term25)))
(let ((e26 (! (>= e14 e4) :named term26)))
(let ((e27 (! (< e4 e5) :named term27)))
(let ((e28 (! (< e11 e5) :named term28)))
(let ((e29 (! (>= e12 e12) :named term29)))
(let ((e30 (! (> e6 e13) :named term30)))
(let ((e31 (! (distinct e13 e12) :named term31)))
(let ((e32 (! (> e17 e14) :named term32)))
(let ((e33 (! (>= e17 e3) :named term33)))
(let ((e34 (! (>= e14 e14) :named term34)))
(let ((e35 (! (= e3 e4) :named term35)))
(let ((e36 (! (distinct e6 v0) :named term36)))
(let ((e37 (! (>= e6 e16) :named term37)))
(let ((e38 (! (> e16 e12) :named term38)))
(let ((e39 (! (< e11 v0) :named term39)))
(let ((e40 (! (<= e14 e11) :named term40)))
(let ((e41 (! (>= e4 e17) :named term41)))
(let ((e42 (! (<= e14 e5) :named term42)))
(let ((e43 (! (> e17 e5) :named term43)))
(let ((e44 (! (>= e4 e16) :named term44)))
(let ((e45 (! (distinct e5 e17) :named term45)))
(let ((e46 (! (> e4 e4) :named term46)))
(let ((e47 (! (>= e4 e11) :named term47)))
(let ((e48 (! (<= e13 e15) :named term48)))
(let ((e49 (! (and e31 e46) :named term49)))
(let ((e50 (! (ite e48 e22 e44) :named term50)))
(let ((e51 (! (=> e40 e47) :named term51)))
(let ((e52 (! (and e32 e27) :named term52)))
(let ((e53 (! (= e38 e25) :named term53)))
(let ((e54 (! (or e30 e33) :named term54)))
(let ((e55 (! (=> e51 e45) :named term55)))
(let ((e56 (! (or e42 e34) :named term56)))
(let ((e57 (! (= e18 e7) :named term57)))
(let ((e58 (! (ite e19 e8 e50) :named term58)))
(let ((e59 (! (not e21) :named term59)))
(let ((e60 (! (and e49 e41) :named term60)))
(let ((e61 (! (ite e39 e54 e43) :named term61)))
(let ((e62 (! (= e55 e60) :named term62)))
(let ((e63 (! (and e26 e59) :named term63)))
(let ((e64 (! (or e36 e52) :named term64)))
(let ((e65 (! (ite e10 e24 e58) :named term65)))
(let ((e66 (! (or e20 e23) :named term66)))
(let ((e67 (! (not e37) :named term67)))
(let ((e68 (! (= e57 e66) :named term68)))
(let ((e69 (! (and e65 e64) :named term69)))
(let ((e70 (! (= e9 e35) :named term70)))
(let ((e71 (! (=> e29 e53) :named term71)))
(let ((e72 (! (ite e63 e71 e62) :named term72)))
(let ((e73 (! (not e72) :named term73)))
(let ((e74 (! (or e69 e70) :named term74)))
(let ((e75 (! (and e61 e67) :named term75)))
(let ((e76 (! (or e73 e56) :named term76)))
(let ((e77 (! (and e76 e75) :named term77)))
(let ((e78 (! (and e68 e68) :named term78)))
(let ((e79 (! (and e78 e77) :named term79)))
(let ((e80 (! (= e79 e74) :named term80)))
(let ((e81 (! (or e80 e28) :named term81)))
e81
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
(get-value (term2))
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
