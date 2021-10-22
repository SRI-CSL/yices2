(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UFBV)
(declare-fun f0 ( (_ BitVec 2)) (_ BitVec 16))
(declare-fun f1 ( (_ BitVec 15)) (_ BitVec 7))
(declare-fun p0 ( (_ BitVec 13) (_ BitVec 11) (_ BitVec 11)) Bool)
(declare-fun p1 ( (_ BitVec 6)) Bool)
(declare-fun v0 () (_ BitVec 2))
(declare-fun v1 () (_ BitVec 12))
(declare-fun v2 () (_ BitVec 10))
(declare-fun v3 () (_ BitVec 5))
(assert (let ((e4(_ bv870 10)))
(let ((e5(_ bv75 8)))
(let ((e6 (! (ite (p0 ((_ zero_extend 1) v1) ((_ zero_extend 3) e5) ((_ sign_extend 1) v2)) (_ bv1 1) (_ bv0 1)) :named term6)))
(let ((e7 (! (f0 ((_ zero_extend 1) e6)) :named term7)))
(let ((e8 (! (ite (bvsge v2 ((_ zero_extend 2) e5)) (_ bv1 1) (_ bv0 1)) :named term8)))
(let ((e9 (! (f1 ((_ sign_extend 10) v3)) :named term9)))
(let ((e10 (! (bvnot e6) :named term10)))
(let ((e11 (! (ite (p1 ((_ extract 8 3) v2)) (_ bv1 1) (_ bv0 1)) :named term11)))
(let ((e12 (! (ite (= (_ bv1 1) ((_ extract 0 0) e6)) e10 e6) :named term12)))
(let ((e13 (! (bvnor ((_ zero_extend 6) e11) e9) :named term13)))
(let ((e14 (! (bvlshr ((_ sign_extend 5) v0) e13) :named term14)))
(let ((e15 (! (ite (bvult e7 ((_ zero_extend 15) e12)) (_ bv1 1) (_ bv0 1)) :named term15)))
(let ((e16 (! (bvnot e14) :named term16)))
(let ((e17 (! ((_ sign_extend 8) e15) :named term17)))
(let ((e18 (! (bvand v3 ((_ zero_extend 4) e15)) :named term18)))
(let ((e19 (! (ite (= e11 e15) (_ bv1 1) (_ bv0 1)) :named term19)))
(let ((e20 (! ((_ extract 2 0) e14) :named term20)))
(let ((e21 (! (ite (bvsge e9 e9) (_ bv1 1) (_ bv0 1)) :named term21)))
(let ((e22 (! (concat v3 e16) :named term22)))
(let ((e23 (! (bvnot v1) :named term23)))
(let ((e24 (! (ite (bvule ((_ zero_extend 4) e20) e14) (_ bv1 1) (_ bv0 1)) :named term24)))
(let ((e25 (! (bvnand e24 e15) :named term25)))
(let ((e26 (! ((_ sign_extend 15) e11) :named term26)))
(let ((e27 (! (ite (= (_ bv1 1) ((_ extract 0 0) e7)) ((_ sign_extend 11) e8) v1) :named term27)))
(let ((e28 (! (ite (bvsle e19 e10) (_ bv1 1) (_ bv0 1)) :named term28)))
(let ((e29 (! (f0 v0) :named term29)))
(let ((e30 (! (bvnor e4 ((_ zero_extend 9) e12)) :named term30)))
(let ((e31 (! (bvslt e10 e19) :named term31)))
(let ((e32 (! (p1 ((_ sign_extend 5) e25)) :named term32)))
(let ((e33 (! (p0 ((_ sign_extend 1) e22) ((_ extract 11 1) e22) ((_ sign_extend 10) e24)) :named term33)))
(let ((e34 (! (p0 ((_ extract 15 3) e7) ((_ zero_extend 2) e17) ((_ sign_extend 6) v3)) :named term34)))
(let ((e35 (! (p0 ((_ extract 13 1) e29) ((_ zero_extend 10) e19) ((_ zero_extend 4) e16)) :named term35)))
(let ((e36 (! (bvslt ((_ zero_extend 9) e6) v2) :named term36)))
(let ((e37 (! (p1 ((_ extract 6 1) e30)) :named term37)))
(let ((e38 (! (bvsge e23 ((_ sign_extend 11) e6)) :named term38)))
(let ((e39 (! (bvugt e4 ((_ sign_extend 9) e11)) :named term39)))
(let ((e40 (! (bvsgt ((_ sign_extend 7) e20) v2) :named term40)))
(let ((e41 (! (bvult ((_ zero_extend 15) e15) e26) :named term41)))
(let ((e42 (! (bvsgt ((_ sign_extend 9) e12) e4) :named term42)))
(let ((e43 (! (bvult ((_ sign_extend 5) v0) e14) :named term43)))
(let ((e44 (! (p1 ((_ extract 10 5) e22)) :named term44)))
(let ((e45 (! (p0 ((_ sign_extend 1) e22) ((_ zero_extend 10) e12) ((_ extract 10 0) e29)) :named term45)))
(let ((e46 (! (distinct e9 e14) :named term46)))
(let ((e47 (! (bvult e22 ((_ sign_extend 11) e8)) :named term47)))
(let ((e48 (! (bvsge v1 e22) :named term48)))
(let ((e49 (! (= e4 ((_ sign_extend 1) e17)) :named term49)))
(let ((e50 (! (bvslt ((_ zero_extend 5) e13) e27) :named term50)))
(let ((e51 (! (bvsge ((_ sign_extend 9) e21) e30) :named term51)))
(let ((e52 (! (p0 ((_ sign_extend 10) e20) ((_ sign_extend 4) e14) ((_ zero_extend 9) v0)) :named term52)))
(let ((e53 (! (bvult e24 e11) :named term53)))
(let ((e54 (! (p1 ((_ extract 6 1) e9)) :named term54)))
(let ((e55 (! (bvult e4 ((_ sign_extend 9) e24)) :named term55)))
(let ((e56 (! (distinct e5 ((_ sign_extend 6) v0)) :named term56)))
(let ((e57 (! (distinct ((_ zero_extend 13) e20) e29) :named term57)))
(let ((e58 (! (bvsge e16 ((_ sign_extend 6) e8)) :named term58)))
(let ((e59 (! (distinct e27 ((_ zero_extend 5) e14)) :named term59)))
(let ((e60 (! (bvsge e14 ((_ zero_extend 2) e18)) :named term60)))
(let ((e61 (! (bvslt ((_ zero_extend 6) e21) e16) :named term61)))
(let ((e62 (! (bvsle ((_ zero_extend 6) e12) e16) :named term62)))
(let ((e63 (! (bvsge v2 ((_ sign_extend 9) e8)) :named term63)))
(let ((e64 (! (bvslt ((_ zero_extend 5) e16) e27) :named term64)))
(let ((e65 (! (bvugt ((_ zero_extend 5) e14) v1) :named term65)))
(let ((e66 (! (bvult ((_ sign_extend 9) e28) v2) :named term66)))
(let ((e67 (! (or e39 e64) :named term67)))
(let ((e68 (! (xor e47 e61) :named term68)))
(let ((e69 (! (xor e49 e40) :named term69)))
(let ((e70 (! (ite e48 e41 e51) :named term70)))
(let ((e71 (! (= e37 e50) :named term71)))
(let ((e72 (! (and e35 e32) :named term72)))
(let ((e73 (! (or e70 e54) :named term73)))
(let ((e74 (! (and e45 e65) :named term74)))
(let ((e75 (! (= e62 e59) :named term75)))
(let ((e76 (! (not e66) :named term76)))
(let ((e77 (! (= e38 e52) :named term77)))
(let ((e78 (! (=> e67 e77) :named term78)))
(let ((e79 (! (=> e71 e31) :named term79)))
(let ((e80 (! (=> e69 e74) :named term80)))
(let ((e81 (! (xor e56 e42) :named term81)))
(let ((e82 (! (not e73) :named term82)))
(let ((e83 (! (not e72) :named term83)))
(let ((e84 (! (=> e83 e63) :named term84)))
(let ((e85 (! (= e36 e57) :named term85)))
(let ((e86 (! (=> e58 e44) :named term86)))
(let ((e87 (! (=> e75 e34) :named term87)))
(let ((e88 (! (not e87) :named term88)))
(let ((e89 (! (not e33) :named term89)))
(let ((e90 (! (xor e86 e85) :named term90)))
(let ((e91 (! (ite e43 e55 e88) :named term91)))
(let ((e92 (! (= e68 e46) :named term92)))
(let ((e93 (! (=> e78 e81) :named term93)))
(let ((e94 (! (and e79 e76) :named term94)))
(let ((e95 (! (= e60 e80) :named term95)))
(let ((e96 (! (not e82) :named term96)))
(let ((e97 (! (=> e84 e53) :named term97)))
(let ((e98 (! (=> e96 e96) :named term98)))
(let ((e99 (! (= e98 e97) :named term99)))
(let ((e100 (! (not e94) :named term100)))
(let ((e101 (! (=> e92 e89) :named term101)))
(let ((e102 (! (ite e99 e101 e101) :named term102)))
(let ((e103 (! (ite e90 e102 e95) :named term103)))
(let ((e104 (! (=> e100 e103) :named term104)))
(let ((e105 (! (ite e91 e104 e91) :named term105)))
(let ((e106 (! (and e93 e105) :named term106)))
e106
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
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
(get-value (term101))
(get-value (term102))
(get-value (term103))
(get-value (term104))
(get-value (term105))
(get-value (term106))
(get-info :all-statistics)
