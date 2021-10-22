(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_AUFBV)
(declare-fun v0 () (_ BitVec 2))
(declare-fun v1 () (_ BitVec 16))
(declare-fun a2 () (Array  (_ BitVec 10)  (_ BitVec 13)))
(declare-fun a3 () (Array  (_ BitVec 16)  (_ BitVec 16)))
(assert (let ((e4(_ bv1606 13)))
(let ((e5 (! (bvand v1 ((_ sign_extend 14) v0)) :named term5)))
(let ((e6 (! (bvxor e5 ((_ zero_extend 3) e4)) :named term6)))
(let ((e7 (! (store a2 ((_ extract 9 0) e4) e4) :named term7)))
(let ((e8 (! (select a3 e6) :named term8)))
(let ((e9 (! (store a2 ((_ extract 10 1) e8) ((_ extract 12 0) v1)) :named term9)))
(let ((e10 (! (bvadd e5 e5) :named term10)))
(let ((e11 (! (bvnor e5 ((_ zero_extend 14) v0)) :named term11)))
(let ((e12 (! (bvor v1 e11) :named term12)))
(let ((e13 (! ((_ extract 1 0) v0) :named term13)))
(let ((e14 (! (bvsub ((_ zero_extend 3) e4) e11) :named term14)))
(let ((e15 (! (bvadd e6 e12) :named term15)))
(let ((e16 (! (bvneg e5) :named term16)))
(let ((e17 (! (bvsrem ((_ sign_extend 3) e4) e12) :named term17)))
(let ((e18 (! (bvxnor e5 e5) :named term18)))
(let ((e19 (! (bvlshr ((_ zero_extend 3) e4) e12) :named term19)))
(let ((e20 (! (ite (= e17 e6) (_ bv1 1) (_ bv0 1)) :named term20)))
(let ((e21 (! (ite (bvslt e8 ((_ sign_extend 3) e4)) (_ bv1 1) (_ bv0 1)) :named term21)))
(let ((e22 (! (bvult e4 ((_ zero_extend 11) e13)) :named term22)))
(let ((e23 (! (bvult ((_ sign_extend 15) e20) e11) :named term23)))
(let ((e24 (! (bvsgt e17 e11) :named term24)))
(let ((e25 (! (bvugt e6 ((_ zero_extend 15) e21)) :named term25)))
(let ((e26 (! (bvsle v1 e18) :named term26)))
(let ((e27 (! (= e6 e11) :named term27)))
(let ((e28 (! (bvuge e10 e16) :named term28)))
(let ((e29 (! (distinct ((_ sign_extend 14) v0) e6) :named term29)))
(let ((e30 (! (bvslt e16 ((_ sign_extend 3) e4)) :named term30)))
(let ((e31 (! (bvslt e18 ((_ sign_extend 14) v0)) :named term31)))
(let ((e32 (! (bvuge ((_ zero_extend 14) v0) e19) :named term32)))
(let ((e33 (! (bvuge e5 e19) :named term33)))
(let ((e34 (! (bvule ((_ sign_extend 11) e13) e4) :named term34)))
(let ((e35 (! (bvsgt v1 e5) :named term35)))
(let ((e36 (! (bvsgt e14 e16) :named term36)))
(let ((e37 (! (bvugt e18 e10) :named term37)))
(let ((e38 (! (bvugt ((_ sign_extend 15) e20) v1) :named term38)))
(let ((e39 (! (bvsgt e8 v1) :named term39)))
(let ((e40 (! (distinct ((_ sign_extend 14) v0) e17) :named term40)))
(let ((e41 (! (bvult ((_ zero_extend 15) e21) e17) :named term41)))
(let ((e42 (! (= e11 ((_ sign_extend 14) v0)) :named term42)))
(let ((e43 (! (bvuge e16 e14) :named term43)))
(let ((e44 (! (= e17 e19) :named term44)))
(let ((e45 (! (bvsgt e17 e10) :named term45)))
(let ((e46 (! (bvule v1 ((_ sign_extend 3) e4)) :named term46)))
(let ((e47 (! (distinct e16 ((_ zero_extend 14) e13)) :named term47)))
(let ((e48 (! (bvuge e17 e10) :named term48)))
(let ((e49 (! (bvsgt e5 ((_ sign_extend 15) e21)) :named term49)))
(let ((e50 (! (bvsge e4 ((_ sign_extend 12) e21)) :named term50)))
(let ((e51 (! (bvugt e17 ((_ zero_extend 14) v0)) :named term51)))
(let ((e52 (! (bvugt e19 v1) :named term52)))
(let ((e53 (! (bvsgt e11 e18) :named term53)))
(let ((e54 (! (bvugt ((_ zero_extend 14) e13) e17) :named term54)))
(let ((e55 (! (bvult e8 e18) :named term55)))
(let ((e56 (! (bvsle ((_ sign_extend 3) e4) e8) :named term56)))
(let ((e57 (! (bvsge ((_ sign_extend 15) e20) e10) :named term57)))
(let ((e58 (! (= e12 e5) :named term58)))
(let ((e59 (! (bvuge e4 ((_ zero_extend 12) e20)) :named term59)))
(let ((e60 (! (bvsge e16 v1) :named term60)))
(let ((e61 (! (bvsle e16 e17) :named term61)))
(let ((e62 (! (bvsle v1 e10) :named term62)))
(let ((e63 (! (bvsle e18 ((_ sign_extend 15) e20)) :named term63)))
(let ((e64 (! (bvuge e14 e15) :named term64)))
(let ((e65 (! (= e39 e43) :named term65)))
(let ((e66 (! (= e30 e44) :named term66)))
(let ((e67 (! (ite e52 e33 e60) :named term67)))
(let ((e68 (! (= e65 e46) :named term68)))
(let ((e69 (! (and e36 e58) :named term69)))
(let ((e70 (! (xor e61 e31) :named term70)))
(let ((e71 (! (= e50 e70) :named term71)))
(let ((e72 (! (ite e49 e71 e40) :named term72)))
(let ((e73 (! (xor e26 e67) :named term73)))
(let ((e74 (! (not e57) :named term74)))
(let ((e75 (! (xor e72 e45) :named term75)))
(let ((e76 (! (ite e34 e59 e51) :named term76)))
(let ((e77 (! (xor e55 e27) :named term77)))
(let ((e78 (! (and e42 e64) :named term78)))
(let ((e79 (! (not e48) :named term79)))
(let ((e80 (! (=> e74 e63) :named term80)))
(let ((e81 (! (xor e66 e24) :named term81)))
(let ((e82 (! (or e68 e53) :named term82)))
(let ((e83 (! (xor e81 e82) :named term83)))
(let ((e84 (! (=> e35 e56) :named term84)))
(let ((e85 (! (= e75 e80) :named term85)))
(let ((e86 (! (ite e28 e25 e62) :named term86)))
(let ((e87 (! (xor e32 e73) :named term87)))
(let ((e88 (! (or e76 e38) :named term88)))
(let ((e89 (! (ite e79 e88 e77) :named term89)))
(let ((e90 (! (= e87 e89) :named term90)))
(let ((e91 (! (not e78) :named term91)))
(let ((e92 (! (=> e90 e22) :named term92)))
(let ((e93 (! (=> e54 e47) :named term93)))
(let ((e94 (! (ite e41 e69 e93) :named term94)))
(let ((e95 (! (ite e83 e84 e83) :named term95)))
(let ((e96 (! (= e37 e37) :named term96)))
(let ((e97 (! (ite e85 e96 e29) :named term97)))
(let ((e98 (! (not e94) :named term98)))
(let ((e99 (! (or e86 e91) :named term99)))
(let ((e100 (! (ite e95 e92 e23) :named term100)))
(let ((e101 (! (ite e100 e100 e98) :named term101)))
(let ((e102 (! (and e97 e97) :named term102)))
(let ((e103 (! (not e99) :named term103)))
(let ((e104 (! (or e103 e102) :named term104)))
(let ((e105 (! (not e104) :named term105)))
(let ((e106 (! (or e101 e101) :named term106)))
(let ((e107 (! (or e106 e106) :named term107)))
(let ((e108 (! (= e107 e105) :named term108)))
(let ((e109 (! (and e108 (not (= e12 (_ bv0 16)))) :named term109)))
(let ((e110 (! (and e109 (not (= e12 (bvnot (_ bv0 16))))) :named term110)))
e110
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
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
(get-value (term107))
(get-value (term108))
(get-value (term109))
(get-value (term110))
(get-info :all-statistics)
