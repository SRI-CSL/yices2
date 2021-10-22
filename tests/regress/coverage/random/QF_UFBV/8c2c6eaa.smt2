(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UFBV)
(declare-fun f0 ( (_ BitVec 4) (_ BitVec 7) (_ BitVec 12)) (_ BitVec 16))
(declare-fun f1 ( (_ BitVec 8)) (_ BitVec 9))
(declare-fun p0 ( (_ BitVec 4) (_ BitVec 16) (_ BitVec 15)) Bool)
(declare-fun p1 ( (_ BitVec 15) (_ BitVec 8) (_ BitVec 15)) Bool)
(declare-fun v0 () (_ BitVec 7))
(declare-fun v1 () (_ BitVec 11))
(declare-fun v2 () (_ BitVec 2))
(declare-fun v3 () (_ BitVec 4))
(assert (let ((e4(_ bv5 5)))
(let ((e5(_ bv1822 11)))
(let ((e6 (! (ite (= (_ bv1 1) ((_ extract 0 0) v2)) ((_ sign_extend 9) v2) e5) :named term6)))
(let ((e7 (! (f0 ((_ extract 8 5) e5) v0 ((_ zero_extend 1) v1)) :named term7)))
(let ((e8 (! (f1 ((_ zero_extend 4) v3)) :named term8)))
(let ((e9 (! (bvsrem ((_ zero_extend 12) v3) e7) :named term9)))
(let ((e10 (! (ite (p0 ((_ extract 6 3) v0) ((_ sign_extend 14) v2) ((_ zero_extend 13) v2)) (_ bv1 1) (_ bv0 1)) :named term10)))
(let ((e11 (! (ite (p1 ((_ zero_extend 4) v1) ((_ extract 7 0) e6) ((_ extract 14 0) e9)) (_ bv1 1) (_ bv0 1)) :named term11)))
(let ((e12 (! (bvashr e7 ((_ sign_extend 9) v0)) :named term12)))
(let ((e13 (! ((_ rotate_right 0) e8) :named term13)))
(let ((e14 (! (ite (bvslt ((_ zero_extend 7) e8) e12) (_ bv1 1) (_ bv0 1)) :named term14)))
(let ((e15 (! (bvnor v1 v1) :named term15)))
(let ((e16 (! (bvor e13 ((_ zero_extend 7) v2)) :named term16)))
(let ((e17 (! ((_ rotate_right 0) e14) :named term17)))
(let ((e18 (! (bvcomp ((_ sign_extend 10) e17) e6) :named term18)))
(let ((e19 (! (ite (bvsge ((_ sign_extend 5) v1) e12) (_ bv1 1) (_ bv0 1)) :named term19)))
(let ((e20 (! (ite (bvugt e7 e9) (_ bv1 1) (_ bv0 1)) :named term20)))
(let ((e21 (! ((_ extract 7 3) e16) :named term21)))
(let ((e22 (! ((_ repeat 1) e21) :named term22)))
(let ((e23 (! (ite (bvsge e8 ((_ sign_extend 8) e14)) (_ bv1 1) (_ bv0 1)) :named term23)))
(let ((e24 (! (bvneg e9) :named term24)))
(let ((e25 (! (ite (distinct e4 ((_ sign_extend 4) e17)) (_ bv1 1) (_ bv0 1)) :named term25)))
(let ((e26 (! (p1 ((_ zero_extend 14) e19) ((_ extract 13 6) e24) ((_ sign_extend 6) e13)) :named term26)))
(let ((e27 (! (p0 ((_ zero_extend 3) e17) ((_ sign_extend 15) e17) ((_ sign_extend 14) e17)) :named term27)))
(let ((e28 (! (bvslt v1 e5) :named term28)))
(let ((e29 (! (bvule v2 ((_ sign_extend 1) e23)) :named term29)))
(let ((e30 (! (bvugt ((_ sign_extend 11) e21) e9) :named term30)))
(let ((e31 (! (p0 ((_ extract 4 1) e21) ((_ sign_extend 15) e10) ((_ zero_extend 6) e13)) :named term31)))
(let ((e32 (! (p1 ((_ sign_extend 6) e8) ((_ sign_extend 4) v3) ((_ zero_extend 10) e21)) :named term32)))
(let ((e33 (! (= ((_ sign_extend 4) e17) e22) :named term33)))
(let ((e34 (! (= ((_ sign_extend 8) e19) e8) :named term34)))
(let ((e35 (! (bvult e7 ((_ zero_extend 15) e19)) :named term35)))
(let ((e36 (! (bvsgt e19 e17) :named term36)))
(let ((e37 (! (bvult e23 e19) :named term37)))
(let ((e38 (! (bvsle e8 ((_ zero_extend 8) e20)) :named term38)))
(let ((e39 (! (p0 ((_ zero_extend 3) e23) ((_ zero_extend 15) e20) ((_ zero_extend 13) v2)) :named term39)))
(let ((e40 (! (bvult e7 ((_ sign_extend 15) e20)) :named term40)))
(let ((e41 (! (bvule e21 ((_ zero_extend 4) e20)) :named term41)))
(let ((e42 (! (bvule e21 ((_ sign_extend 3) v2)) :named term42)))
(let ((e43 (! (bvsge e6 ((_ zero_extend 10) e17)) :named term43)))
(let ((e44 (! (distinct e9 ((_ sign_extend 11) e22)) :named term44)))
(let ((e45 (! (bvule e7 ((_ zero_extend 7) e16)) :named term45)))
(let ((e46 (! (bvslt e15 e5) :named term46)))
(let ((e47 (! (bvule e23 e25) :named term47)))
(let ((e48 (! (bvsgt ((_ sign_extend 6) e22) e15) :named term48)))
(let ((e49 (! (bvsge v3 ((_ zero_extend 3) e25)) :named term49)))
(let ((e50 (! (bvslt v1 ((_ zero_extend 10) e20)) :named term50)))
(let ((e51 (! (bvsle ((_ zero_extend 4) e23) e4) :named term51)))
(let ((e52 (! (bvult ((_ zero_extend 4) e23) e21) :named term52)))
(let ((e53 (! (bvslt e24 ((_ sign_extend 15) e14)) :named term53)))
(let ((e54 (! (p0 ((_ extract 4 1) e5) ((_ zero_extend 11) e22) ((_ extract 14 0) e7)) :named term54)))
(let ((e55 (! (bvule v1 ((_ sign_extend 9) v2)) :named term55)))
(let ((e56 (! (bvsle e24 e12) :named term56)))
(let ((e57 (! (distinct ((_ zero_extend 1) e19) v2) :named term57)))
(let ((e58 (! (p1 ((_ sign_extend 14) e19) ((_ extract 8 1) e9) ((_ zero_extend 14) e23)) :named term58)))
(let ((e59 (! (= ((_ sign_extend 4) e25) e22) :named term59)))
(let ((e60 (! (bvugt e19 e10) :named term60)))
(let ((e61 (! (bvsgt e10 e25) :named term61)))
(let ((e62 (! (bvsge e15 ((_ zero_extend 9) v2)) :named term62)))
(let ((e63 (! (bvsle ((_ sign_extend 6) e22) v1) :named term63)))
(let ((e64 (! (bvuge e6 ((_ zero_extend 10) e10)) :named term64)))
(let ((e65 (! (bvsge e4 ((_ zero_extend 4) e19)) :named term65)))
(let ((e66 (! (bvsgt e18 e19) :named term66)))
(let ((e67 (! (bvsgt ((_ zero_extend 4) e14) e21) :named term67)))
(let ((e68 (! (bvugt ((_ sign_extend 15) e17) e12) :named term68)))
(let ((e69 (! (bvsle e8 e16) :named term69)))
(let ((e70 (! (distinct e4 ((_ zero_extend 4) e20)) :named term70)))
(let ((e71 (! (p1 ((_ sign_extend 11) v3) ((_ sign_extend 7) e14) ((_ sign_extend 6) e8)) :named term71)))
(let ((e72 (! (bvule e9 ((_ zero_extend 15) e10)) :named term72)))
(let ((e73 (! (bvsgt ((_ zero_extend 11) e22) e9) :named term73)))
(let ((e74 (! (= ((_ zero_extend 3) v2) e21) :named term74)))
(let ((e75 (! (bvult ((_ sign_extend 5) v2) v0) :named term75)))
(let ((e76 (! (= e7 ((_ zero_extend 15) e20)) :named term76)))
(let ((e77 (! (= e19 e14) :named term77)))
(let ((e78 (! (bvuge e25 e11) :named term78)))
(let ((e79 (! (=> e43 e26) :named term79)))
(let ((e80 (! (=> e38 e79) :named term80)))
(let ((e81 (! (and e36 e53) :named term81)))
(let ((e82 (! (and e70 e74) :named term82)))
(let ((e83 (! (ite e72 e48 e55) :named term83)))
(let ((e84 (! (ite e69 e35 e40) :named term84)))
(let ((e85 (! (= e28 e32) :named term85)))
(let ((e86 (! (= e78 e83) :named term86)))
(let ((e87 (! (xor e67 e62) :named term87)))
(let ((e88 (! (=> e37 e27) :named term88)))
(let ((e89 (! (and e76 e77) :named term89)))
(let ((e90 (! (and e47 e47) :named term90)))
(let ((e91 (! (or e50 e42) :named term91)))
(let ((e92 (! (= e41 e41) :named term92)))
(let ((e93 (! (=> e63 e87) :named term93)))
(let ((e94 (! (xor e58 e73) :named term94)))
(let ((e95 (! (not e61) :named term95)))
(let ((e96 (! (and e81 e94) :named term96)))
(let ((e97 (! (and e54 e51) :named term97)))
(let ((e98 (! (or e95 e97) :named term98)))
(let ((e99 (! (and e44 e39) :named term99)))
(let ((e100 (! (= e71 e64) :named term100)))
(let ((e101 (! (not e46) :named term101)))
(let ((e102 (! (or e91 e34) :named term102)))
(let ((e103 (! (not e60) :named term103)))
(let ((e104 (! (or e65 e101) :named term104)))
(let ((e105 (! (=> e84 e45) :named term105)))
(let ((e106 (! (xor e90 e59) :named term106)))
(let ((e107 (! (ite e99 e30 e66) :named term107)))
(let ((e108 (! (= e107 e105) :named term108)))
(let ((e109 (! (= e75 e89) :named term109)))
(let ((e110 (! (xor e29 e56) :named term110)))
(let ((e111 (! (=> e80 e80) :named term111)))
(let ((e112 (! (xor e100 e109) :named term112)))
(let ((e113 (! (=> e52 e111) :named term113)))
(let ((e114 (! (not e86) :named term114)))
(let ((e115 (! (= e98 e108) :named term115)))
(let ((e116 (! (ite e110 e82 e112) :named term116)))
(let ((e117 (! (or e93 e85) :named term117)))
(let ((e118 (! (or e113 e116) :named term118)))
(let ((e119 (! (= e49 e49) :named term119)))
(let ((e120 (! (= e118 e57) :named term120)))
(let ((e121 (! (= e117 e88) :named term121)))
(let ((e122 (! (and e103 e103) :named term122)))
(let ((e123 (! (xor e33 e114) :named term123)))
(let ((e124 (! (= e31 e115) :named term124)))
(let ((e125 (! (and e124 e123) :named term125)))
(let ((e126 (! (not e122) :named term126)))
(let ((e127 (! (not e104) :named term127)))
(let ((e128 (! (= e127 e120) :named term128)))
(let ((e129 (! (xor e119 e121) :named term129)))
(let ((e130 (! (xor e68 e125) :named term130)))
(let ((e131 (! (ite e92 e102 e92) :named term131)))
(let ((e132 (! (xor e130 e106) :named term132)))
(let ((e133 (! (= e126 e126) :named term133)))
(let ((e134 (! (= e131 e129) :named term134)))
(let ((e135 (! (xor e128 e133) :named term135)))
(let ((e136 (! (or e96 e135) :named term136)))
(let ((e137 (! (and e134 e134) :named term137)))
(let ((e138 (! (ite e136 e132 e137) :named term138)))
(let ((e139 (! (and e138 (not (= e7 (_ bv0 16)))) :named term139)))
(let ((e140 (! (and e139 (not (= e7 (bvnot (_ bv0 16))))) :named term140)))
e140
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
(get-value (term107))
(get-value (term108))
(get-value (term109))
(get-value (term110))
(get-value (term111))
(get-value (term112))
(get-value (term113))
(get-value (term114))
(get-value (term115))
(get-value (term116))
(get-value (term117))
(get-value (term118))
(get-value (term119))
(get-value (term120))
(get-value (term121))
(get-value (term122))
(get-value (term123))
(get-value (term124))
(get-value (term125))
(get-value (term126))
(get-value (term127))
(get-value (term128))
(get-value (term129))
(get-value (term130))
(get-value (term131))
(get-value (term132))
(get-value (term133))
(get-value (term134))
(get-value (term135))
(get-value (term136))
(get-value (term137))
(get-value (term138))
(get-value (term139))
(get-value (term140))
(get-info :all-statistics)
