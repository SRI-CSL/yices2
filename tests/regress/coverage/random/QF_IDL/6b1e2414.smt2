(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_IDL)
(declare-fun v0 () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun v3 () Int)
(declare-fun v4 () Int)
(declare-fun v5 () Int)
(declare-fun v6 () Int)
(assert (let ((e7 15))
(let ((e8 (! 10 :named term8)))
(let ((e9 (! 0 :named term9)))
(let ((e10 (! 2 :named term10)))
(let ((e11 (! 0 :named term11)))
(let ((e12 (! 4 :named term12)))
(let ((e13 (! (distinct v1 v0) :named term13)))
(let ((e14 (! (distinct (- v5 v2) e7) :named term14)))
(let ((e15 (! (>= (- v3 v1) (- e12)) :named term15)))
(let ((e16 (! (<= v6 v6) :named term16)))
(let ((e17 (! (distinct v4 v0) :named term17)))
(let ((e18 (! (> (- v3 v3) e8) :named term18)))
(let ((e19 (! (> v5 v2) :named term19)))
(let ((e20 (! (< v1 v2) :named term20)))
(let ((e21 (! (distinct (- v3 v4) (- e12)) :named term21)))
(let ((e22 (! (distinct (- v2 v0) (- e10)) :named term22)))
(let ((e23 (! (<= (- v1 v4) (- e8)) :named term23)))
(let ((e24 (! (distinct v6 v3) :named term24)))
(let ((e25 (! (<= v4 v0) :named term25)))
(let ((e26 (! (distinct v4 v3) :named term26)))
(let ((e27 (! (= v5 v6) :named term27)))
(let ((e28 (! (distinct v6 v5) :named term28)))
(let ((e29 (! (< (- v2 v0) e8) :named term29)))
(let ((e30 (! (distinct v5 v6) :named term30)))
(let ((e31 (! (> v4 v1) :named term31)))
(let ((e32 (! (> v4 v3) :named term32)))
(let ((e33 (! (> (- v5 v3) e10) :named term33)))
(let ((e34 (! (= (- v1 v1) (- e7)) :named term34)))
(let ((e35 (! (< v3 v3) :named term35)))
(let ((e36 (! (> (- v3 v2) e11) :named term36)))
(let ((e37 (! (>= v0 v4) :named term37)))
(let ((e38 (! (>= v6 v5) :named term38)))
(let ((e39 (! (>= v4 v3) :named term39)))
(let ((e40 (! (< v0 v1) :named term40)))
(let ((e41 (! (> (- v5 v6) e7) :named term41)))
(let ((e42 (! (> v0 v0) :named term42)))
(let ((e43 (! (distinct v1 v4) :named term43)))
(let ((e44 (! (<= (- v1 v5) (- e9)) :named term44)))
(let ((e45 (! (distinct (- v5 v0) e11) :named term45)))
(let ((e46 (! (<= v3 v0) :named term46)))
(let ((e47 (! (distinct v5 v4) :named term47)))
(let ((e48 (! (>= v1 v6) :named term48)))
(let ((e49 (! (= v1 v0) :named term49)))
(let ((e50 (! (distinct v0 v5) :named term50)))
(let ((e51 (! (<= (- v5 v2) (- e8)) :named term51)))
(let ((e52 (! (distinct v3 v6) :named term52)))
(let ((e53 (! (<= v5 v2) :named term53)))
(let ((e54 (! (< v4 v1) :named term54)))
(let ((e55 (! (distinct (- v6 v4) (- e11)) :named term55)))
(let ((e56 (! (and e20 e31) :named term56)))
(let ((e57 (! (= e56 e16) :named term57)))
(let ((e58 (! (and e53 e51) :named term58)))
(let ((e59 (! (= e54 e14) :named term59)))
(let ((e60 (! (= e35 e44) :named term60)))
(let ((e61 (! (=> e23 e30) :named term61)))
(let ((e62 (! (ite e43 e41 e15) :named term62)))
(let ((e63 (! (xor e25 e25) :named term63)))
(let ((e64 (! (or e21 e55) :named term64)))
(let ((e65 (! (not e34) :named term65)))
(let ((e66 (! (xor e59 e58) :named term66)))
(let ((e67 (! (or e22 e65) :named term67)))
(let ((e68 (! (or e36 e37) :named term68)))
(let ((e69 (! (or e64 e32) :named term69)))
(let ((e70 (! (ite e57 e40 e50) :named term70)))
(let ((e71 (! (or e47 e60) :named term71)))
(let ((e72 (! (ite e46 e46 e68) :named term72)))
(let ((e73 (! (= e17 e27) :named term73)))
(let ((e74 (! (not e72) :named term74)))
(let ((e75 (! (ite e67 e49 e24) :named term75)))
(let ((e76 (! (=> e71 e33) :named term76)))
(let ((e77 (! (= e52 e42) :named term77)))
(let ((e78 (! (or e18 e39) :named term78)))
(let ((e79 (! (and e61 e78) :named term79)))
(let ((e80 (! (xor e66 e73) :named term80)))
(let ((e81 (! (= e74 e63) :named term81)))
(let ((e82 (! (or e77 e77) :named term82)))
(let ((e83 (! (and e19 e13) :named term83)))
(let ((e84 (! (xor e76 e28) :named term84)))
(let ((e85 (! (= e48 e29) :named term85)))
(let ((e86 (! (= e79 e62) :named term86)))
(let ((e87 (! (and e26 e81) :named term87)))
(let ((e88 (! (= e86 e86) :named term88)))
(let ((e89 (! (not e85) :named term89)))
(let ((e90 (! (xor e87 e82) :named term90)))
(let ((e91 (! (and e89 e83) :named term91)))
(let ((e92 (! (or e75 e84) :named term92)))
(let ((e93 (! (or e90 e45) :named term93)))
(let ((e94 (! (xor e80 e92) :named term94)))
(let ((e95 (! (or e38 e94) :named term95)))
(let ((e96 (! (or e95 e91) :named term96)))
(let ((e97 (! (xor e96 e88) :named term97)))
(let ((e98 (! (= e69 e70) :named term98)))
(let ((e99 (! (= e98 e93) :named term99)))
(let ((e100 (! (xor e99 e97) :named term100)))
e100
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
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
(get-value (term88))
(get-value (term89))
(get-value (term90))
(get-value (term91))
(get-value (term92))
(get-value (term93))
(get-value (term94))
(get-value (term95))
(get-value (term96))
(get-value (term97))
(get-value (term98))
(get-value (term99))
(get-value (term100))
(get-info :all-statistics)
