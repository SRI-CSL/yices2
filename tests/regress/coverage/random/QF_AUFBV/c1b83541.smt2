(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_AUFBV)
(declare-fun v0 () (_ BitVec 16))
(declare-fun v1 () (_ BitVec 9))
(declare-fun v2 () (_ BitVec 12))
(declare-fun a3 () (Array  (_ BitVec 2)  (_ BitVec 8)))
(assert (let ((e4(_ bv462 10)))
(let ((e5(_ bv6 3)))
(let ((e6 (! (ite (bvult ((_ sign_extend 9) e5) v2) (_ bv1 1) (_ bv0 1)) :named term6)))
(let ((e7 (! ((_ sign_extend 0) v0) :named term7)))
(let ((e8 (! (ite (bvsle ((_ zero_extend 7) v1) v0) (_ bv1 1) (_ bv0 1)) :named term8)))
(let ((e9 (! (bvashr v0 v0) :named term9)))
(let ((e10 (! (bvlshr ((_ sign_extend 4) v2) e9) :named term10)))
(let ((e11 (! (bvlshr e4 ((_ sign_extend 9) e6)) :named term11)))
(let ((e12 (! (store a3 ((_ extract 9 8) e4) ((_ extract 8 1) e7)) :named term12)))
(let ((e13 (! (store e12 ((_ extract 2 1) e5) ((_ extract 9 2) e11)) :named term13)))
(let ((e14 (! (select e13 ((_ extract 5 4) e4)) :named term14)))
(let ((e15 (! (select e12 ((_ extract 4 3) e11)) :named term15)))
(let ((e16 (! (store e13 ((_ zero_extend 1) e8) ((_ sign_extend 7) e6)) :named term16)))
(let ((e17 (! (select e13 ((_ extract 2 1) e15)) :named term17)))
(let ((e18 (! (select a3 ((_ sign_extend 1) e8)) :named term18)))
(let ((e19 (! ((_ sign_extend 4) e18) :named term19)))
(let ((e20 (! ((_ sign_extend 0) e9) :named term20)))
(let ((e21 (! (bvor ((_ sign_extend 1) v1) e4) :named term21)))
(let ((e22 (! (bvmul ((_ zero_extend 2) e4) e19) :named term22)))
(let ((e23 (! (ite (= (_ bv1 1) ((_ extract 5 5) e15)) e20 ((_ sign_extend 6) e4)) :named term23)))
(let ((e24 (! ((_ sign_extend 7) e17) :named term24)))
(let ((e25 (! (ite (bvult e11 ((_ sign_extend 2) e15)) (_ bv1 1) (_ bv0 1)) :named term25)))
(let ((e26 (! (bvsub e7 e10) :named term26)))
(let ((e27 (! (ite (bvugt ((_ zero_extend 7) e8) e15) (_ bv1 1) (_ bv0 1)) :named term27)))
(let ((e28 (! (bvor v0 ((_ sign_extend 15) e27)) :named term28)))
(let ((e29 (! (bvneg v1) :named term29)))
(let ((e30 (! (bvudiv ((_ zero_extend 7) e6) e14) :named term30)))
(let ((e31 (! ((_ zero_extend 1) v2) :named term31)))
(let ((e32 (! (bvnand e29 v1) :named term32)))
(let ((e33 (! (bvand ((_ sign_extend 15) e25) e26) :named term33)))
(let ((e34 (! ((_ rotate_left 0) e5) :named term34)))
(let ((e35 (! (= e25 e6) :named term35)))
(let ((e36 (! (bvuge e10 ((_ zero_extend 3) e31)) :named term36)))
(let ((e37 (! (bvule e11 ((_ sign_extend 2) e17)) :named term37)))
(let ((e38 (! (bvule ((_ zero_extend 13) e5) e20) :named term38)))
(let ((e39 (! (bvsle e15 ((_ sign_extend 7) e25)) :named term39)))
(let ((e40 (! (bvule e14 ((_ sign_extend 7) e6)) :named term40)))
(let ((e41 (! (bvult e22 ((_ sign_extend 2) e4)) :named term41)))
(let ((e42 (! (bvult ((_ zero_extend 6) e11) e7) :named term42)))
(let ((e43 (! (distinct ((_ zero_extend 8) e8) e32) :named term43)))
(let ((e44 (! (bvsgt e7 ((_ sign_extend 6) e11)) :named term44)))
(let ((e45 (! (bvsge e25 e25) :named term45)))
(let ((e46 (! (bvsgt ((_ zero_extend 7) e25) e15) :named term46)))
(let ((e47 (! (bvuge ((_ sign_extend 4) e30) e22) :named term47)))
(let ((e48 (! (bvule ((_ zero_extend 8) e30) e33) :named term48)))
(let ((e49 (! (distinct e26 v0) :named term49)))
(let ((e50 (! (bvslt ((_ sign_extend 15) e6) e26) :named term50)))
(let ((e51 (! (bvsle ((_ sign_extend 6) e21) e20) :named term51)))
(let ((e52 (! (bvule ((_ sign_extend 2) e18) e21) :named term52)))
(let ((e53 (! (bvugt e26 ((_ sign_extend 8) e18)) :named term53)))
(let ((e54 (! (bvugt ((_ zero_extend 11) e6) e19) :named term54)))
(let ((e55 (! (bvsge e33 ((_ sign_extend 4) e22)) :named term55)))
(let ((e56 (! (bvule ((_ sign_extend 1) e29) e4) :named term56)))
(let ((e57 (! (bvult ((_ sign_extend 2) e11) e19) :named term57)))
(let ((e58 (! (bvugt ((_ sign_extend 8) e30) e10) :named term58)))
(let ((e59 (! (bvult e9 e20) :named term59)))
(let ((e60 (! (distinct v0 e9) :named term60)))
(let ((e61 (! (bvslt e33 ((_ zero_extend 13) e34)) :named term61)))
(let ((e62 (! (bvsgt ((_ zero_extend 4) e32) e31) :named term62)))
(let ((e63 (! (bvsle ((_ sign_extend 4) v2) e33) :named term63)))
(let ((e64 (! (bvuge v2 e19) :named term64)))
(let ((e65 (! (bvugt ((_ sign_extend 15) e25) e23) :named term65)))
(let ((e66 (! (bvule ((_ zero_extend 8) e17) v0) :named term66)))
(let ((e67 (! (bvsle ((_ sign_extend 2) e17) e21) :named term67)))
(let ((e68 (! (bvult e10 e7) :named term68)))
(let ((e69 (! (bvugt v0 e20) :named term69)))
(let ((e70 (! (= e33 ((_ sign_extend 8) e14)) :named term70)))
(let ((e71 (! (bvsgt v0 ((_ zero_extend 13) e34)) :named term71)))
(let ((e72 (! (bvult v0 ((_ zero_extend 15) e27)) :named term72)))
(let ((e73 (! (bvugt e4 ((_ zero_extend 9) e25)) :named term73)))
(let ((e74 (! (bvuge e26 ((_ zero_extend 6) e21)) :named term74)))
(let ((e75 (! (bvule v0 ((_ zero_extend 8) e18)) :named term75)))
(let ((e76 (! (bvult ((_ zero_extend 1) e17) e32) :named term76)))
(let ((e77 (! (= ((_ zero_extend 15) e6) e10) :named term77)))
(let ((e78 (! (= e31 ((_ zero_extend 5) e14)) :named term78)))
(let ((e79 (! (bvuge e10 ((_ zero_extend 8) e17)) :named term79)))
(let ((e80 (! (bvugt ((_ zero_extend 1) e14) e32) :named term80)))
(let ((e81 (! (distinct ((_ zero_extend 1) e29) e11) :named term81)))
(let ((e82 (! (distinct e24 ((_ sign_extend 6) v1)) :named term82)))
(let ((e83 (! (bvuge e24 ((_ sign_extend 14) e25)) :named term83)))
(let ((e84 (! (bvuge e4 ((_ zero_extend 1) e29)) :named term84)))
(let ((e85 (! (bvsge ((_ sign_extend 15) e27) e10) :named term85)))
(let ((e86 (! (bvult e15 e15) :named term86)))
(let ((e87 (! (bvult e7 ((_ sign_extend 8) e17)) :named term87)))
(let ((e88 (! (= ((_ sign_extend 8) e27) e32) :named term88)))
(let ((e89 (! (bvslt e20 ((_ zero_extend 15) e27)) :named term89)))
(let ((e90 (! (bvugt e7 e26) :named term90)))
(let ((e91 (! (bvslt ((_ sign_extend 9) e5) v2) :named term91)))
(let ((e92 (! (bvuge ((_ sign_extend 7) e27) e18) :named term92)))
(let ((e93 (! (bvult ((_ sign_extend 4) e22) e23) :named term93)))
(let ((e94 (! (bvslt ((_ sign_extend 4) e19) e28) :named term94)))
(let ((e95 (! (and e54 e92) :named term95)))
(let ((e96 (! (or e80 e74) :named term96)))
(let ((e97 (! (xor e67 e90) :named term97)))
(let ((e98 (! (and e50 e52) :named term98)))
(let ((e99 (! (xor e57 e61) :named term99)))
(let ((e100 (! (= e41 e51) :named term100)))
(let ((e101 (! (xor e43 e46) :named term101)))
(let ((e102 (! (and e55 e49) :named term102)))
(let ((e103 (! (or e83 e42) :named term103)))
(let ((e104 (! (not e98) :named term104)))
(let ((e105 (! (ite e44 e103 e39) :named term105)))
(let ((e106 (! (not e100) :named term106)))
(let ((e107 (! (= e77 e70) :named term107)))
(let ((e108 (! (xor e79 e105) :named term108)))
(let ((e109 (! (=> e101 e87) :named term109)))
(let ((e110 (! (or e40 e40) :named term110)))
(let ((e111 (! (ite e81 e47 e107) :named term111)))
(let ((e112 (! (not e88) :named term112)))
(let ((e113 (! (ite e56 e93 e108) :named term113)))
(let ((e114 (! (and e60 e111) :named term114)))
(let ((e115 (! (=> e75 e45) :named term115)))
(let ((e116 (! (ite e97 e59 e112) :named term116)))
(let ((e117 (! (not e35) :named term117)))
(let ((e118 (! (ite e72 e106 e68) :named term118)))
(let ((e119 (! (and e117 e114) :named term119)))
(let ((e120 (! (not e71) :named term120)))
(let ((e121 (! (not e48) :named term121)))
(let ((e122 (! (= e115 e115) :named term122)))
(let ((e123 (! (or e118 e65) :named term123)))
(let ((e124 (! (xor e96 e84) :named term124)))
(let ((e125 (! (or e66 e119) :named term125)))
(let ((e126 (! (and e36 e110) :named term126)))
(let ((e127 (! (xor e104 e120) :named term127)))
(let ((e128 (! (or e78 e121) :named term128)))
(let ((e129 (! (=> e89 e91) :named term129)))
(let ((e130 (! (or e109 e124) :named term130)))
(let ((e131 (! (and e94 e94) :named term131)))
(let ((e132 (! (= e99 e129) :named term132)))
(let ((e133 (! (not e131) :named term133)))
(let ((e134 (! (xor e128 e62) :named term134)))
(let ((e135 (! (ite e64 e113 e133) :named term135)))
(let ((e136 (! (=> e123 e126) :named term136)))
(let ((e137 (! (and e127 e58) :named term137)))
(let ((e138 (! (or e82 e132) :named term138)))
(let ((e139 (! (and e116 e137) :named term139)))
(let ((e140 (! (or e139 e102) :named term140)))
(let ((e141 (! (xor e136 e122) :named term141)))
(let ((e142 (! (=> e63 e37) :named term142)))
(let ((e143 (! (xor e38 e125) :named term143)))
(let ((e144 (! (and e73 e135) :named term144)))
(let ((e145 (! (ite e138 e85 e138) :named term145)))
(let ((e146 (! (xor e86 e69) :named term146)))
(let ((e147 (! (ite e142 e145 e141) :named term147)))
(let ((e148 (! (not e53) :named term148)))
(let ((e149 (! (xor e146 e147) :named term149)))
(let ((e150 (! (xor e130 e76) :named term150)))
(let ((e151 (! (= e143 e95) :named term151)))
(let ((e152 (! (and e148 e151) :named term152)))
(let ((e153 (! (not e140) :named term153)))
(let ((e154 (! (ite e144 e134 e153) :named term154)))
(let ((e155 (! (ite e154 e152 e149) :named term155)))
(let ((e156 (! (not e155) :named term156)))
(let ((e157 (! (xor e150 e150) :named term157)))
(let ((e158 (! (xor e156 e157) :named term158)))
(let ((e159 (! (and e158 (not (= e14 (_ bv0 8)))) :named term159)))
e159
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
(get-value (term141))
(get-value (term142))
(get-value (term143))
(get-value (term144))
(get-value (term145))
(get-value (term146))
(get-value (term147))
(get-value (term148))
(get-value (term149))
(get-value (term150))
(get-value (term151))
(get-value (term152))
(get-value (term153))
(get-value (term154))
(get-value (term155))
(get-value (term156))
(get-value (term157))
(get-value (term158))
(get-value (term159))
(get-info :all-statistics)
