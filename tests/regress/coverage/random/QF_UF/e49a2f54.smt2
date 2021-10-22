(set-info :source |fuzzsmt|)
(set-info :smt-lib-version 2.0)
(set-info :category "random")
(set-info :status unknown)
(set-logic QF_UF)
(declare-sort S0 0)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-fun v0 () S0)
(declare-fun v1 () S0)
(declare-fun v2 () S0)
(declare-fun v3 () S1)
(declare-fun v4 () S1)
(declare-fun v5 () S1)
(declare-fun v6 () S2)
(declare-fun v7 () S2)
(declare-fun v8 () S2)
(declare-fun f0 ( S2 S2 S1) S2)
(declare-fun f1 ( S2 S0) S1)
(declare-fun f2 ( S0 S1) S2)
(declare-fun f3 ( S1 S2 S0) S1)
(declare-fun f4 ( S1 S1 S2) S0)
(declare-fun p0 ( S0) Bool)
(declare-fun p1 ( S0 S0 S2) Bool)
(declare-fun p2 ( S0 S2) Bool)
(declare-fun p3 ( S2 S0 S0) Bool)
(declare-fun p4 ( S1 S0 S0) Bool)
(assert (let ((e9 (f4 v5 v5 v7)))
(let ((e10 (! (f3 v5 v8 v1) :named term10)))
(let ((e11 (! (f2 v2 v3) :named term11)))
(let ((e12 (! (f2 v2 v4) :named term12)))
(let ((e13 (! (f1 v6 v1) :named term13)))
(let ((e14 (! (f3 v4 e11 v0) :named term14)))
(let ((e15 (! (f3 e10 v8 e9) :named term15)))
(let ((e16 (! (f2 v0 e15) :named term16)))
(let ((e17 (! (f4 v3 v3 e16) :named term17)))
(let ((e18 (! (f0 e12 v7 e13) :named term18)))
(let ((e19 (! (p4 v5 v2 v1) :named term19)))
(let ((e20 (! (p4 v4 e17 v1) :named term20)))
(let ((e21 (! (= v8 e12) :named term21)))
(let ((e22 (! (= v6 v7) :named term22)))
(let ((e23 (! (distinct v0 v1) :named term23)))
(let ((e24 (! (= e15 v4) :named term24)))
(let ((e25 (! (distinct e13 v5) :named term25)))
(let ((e26 (! (= v3 e10) :named term26)))
(let ((e27 (! (= e9 v1) :named term27)))
(let ((e28 (! (= e14 v3) :named term28)))
(let ((e29 (! (= e16 v7) :named term29)))
(let ((e30 (! (p2 v0 e16) :named term30)))
(let ((e31 (! (distinct e18 e16) :named term31)))
(let ((e32 (! (distinct e11 e12) :named term32)))
(let ((e33 (! (p4 v4 v0 v2) :named term33)))
(let ((e34 (! (p2 v0 e16) :named term34)))
(let ((e35 (! (p2 v2 e11) :named term35)))
(let ((e36 (! (p2 v2 e16) :named term36)))
(let ((e37 (! (p0 v2) :named term37)))
(let ((e38 (! (p3 e18 e9 v2) :named term38)))
(let ((e39 (! (p1 v2 e9 e11) :named term39)))
(let ((e40 (! (ite e36 e16 e16) :named term40)))
(let ((e41 (! (ite e29 e14 v5) :named term41)))
(let ((e42 (! (ite e36 e10 v5) :named term42)))
(let ((e43 (! (ite e34 e12 v6) :named term43)))
(let ((e44 (! (ite e35 v8 e11) :named term44)))
(let ((e45 (! (ite e20 v3 e42) :named term45)))
(let ((e46 (! (ite e31 e44 e18) :named term46)))
(let ((e47 (! (ite e25 e13 e15) :named term47)))
(let ((e48 (! (ite e39 v0 v2) :named term48)))
(let ((e49 (! (ite e30 e47 e45) :named term49)))
(let ((e50 (! (ite e32 e9 e17) :named term50)))
(let ((e51 (! (ite e29 v3 e45) :named term51)))
(let ((e52 (! (ite e25 v4 v5) :named term52)))
(let ((e53 (! (ite e29 e49 e52) :named term53)))
(let ((e54 (! (ite e19 e18 v6) :named term54)))
(let ((e55 (! (ite e37 v1 e48) :named term55)))
(let ((e56 (! (ite e21 v7 e11) :named term56)))
(let ((e57 (! (ite e37 e17 e17) :named term57)))
(let ((e58 (! (ite e26 e52 e47) :named term58)))
(let ((e59 (! (ite e23 e15 e51) :named term59)))
(let ((e60 (! (ite e27 e47 e51) :named term60)))
(let ((e61 (! (ite e25 e58 e10) :named term61)))
(let ((e62 (! (ite e22 e40 e46) :named term62)))
(let ((e63 (! (ite e39 e57 e50) :named term63)))
(let ((e64 (! (ite e33 e59 v3) :named term64)))
(let ((e65 (! (ite e28 e57 e17) :named term65)))
(let ((e66 (! (ite e26 e57 e50) :named term66)))
(let ((e67 (! (ite e38 e12 e12) :named term67)))
(let ((e68 (! (ite e24 e49 e13) :named term68)))
(let ((e69 (! (= v6 e16) :named term69)))
(let ((e70 (! (= e55 e17) :named term70)))
(let ((e71 (! (distinct e13 e10) :named term71)))
(let ((e72 (! (distinct e40 e46) :named term72)))
(let ((e73 (! (p4 v5 e17 v2) :named term73)))
(let ((e74 (! (distinct e11 e16) :named term74)))
(let ((e75 (! (p3 e43 e63 e57) :named term75)))
(let ((e76 (! (= e50 e57) :named term76)))
(let ((e77 (! (distinct v0 e57) :named term77)))
(let ((e78 (! (p3 e40 e66 e9) :named term78)))
(let ((e79 (! (distinct e54 v7) :named term79)))
(let ((e80 (! (= e41 v3) :named term80)))
(let ((e81 (! (p0 e9) :named term81)))
(let ((e82 (! (= e67 e46) :named term82)))
(let ((e83 (! (= e14 e53) :named term83)))
(let ((e84 (! (p2 v0 e43) :named term84)))
(let ((e85 (! (p3 e16 e57 e63) :named term85)))
(let ((e86 (! (p4 e10 e63 e65) :named term86)))
(let ((e87 (! (= v1 v1) :named term87)))
(let ((e88 (! (distinct v4 e60) :named term88)))
(let ((e89 (! (p3 e12 e63 e48) :named term89)))
(let ((e90 (! (p1 e17 e55 e40) :named term90)))
(let ((e91 (! (p0 e48) :named term91)))
(let ((e92 (! (p0 e57) :named term92)))
(let ((e93 (! (p0 e50) :named term93)))
(let ((e94 (! (= e59 e45) :named term94)))
(let ((e95 (! (= e52 e10) :named term95)))
(let ((e96 (! (p2 e63 e11) :named term96)))
(let ((e97 (! (p0 e66) :named term97)))
(let ((e98 (! (p1 e66 e48 e40) :named term98)))
(let ((e99 (! (distinct e18 e67) :named term99)))
(let ((e100 (! (p0 v1) :named term100)))
(let ((e101 (! (= e64 e58) :named term101)))
(let ((e102 (! (distinct e56 v7) :named term102)))
(let ((e103 (! (p3 e11 e55 e65) :named term103)))
(let ((e104 (! (p3 v6 e66 e50) :named term104)))
(let ((e105 (! (p4 e42 e17 v2) :named term105)))
(let ((e106 (! (= e68 v5) :named term106)))
(let ((e107 (! (distinct e51 e15) :named term107)))
(let ((e108 (! (= e49 e51) :named term108)))
(let ((e109 (! (distinct e61 e59) :named term109)))
(let ((e110 (! (p1 v0 e17 v8) :named term110)))
(let ((e111 (! (p0 e48) :named term111)))
(let ((e112 (! (distinct e44 e18) :named term112)))
(let ((e113 (! (= e62 e12) :named term113)))
(let ((e114 (! (= e47 e42) :named term114)))
(let ((e115 (! (=> e104 e94) :named term115)))
(let ((e116 (! (and e89 e83) :named term116)))
(let ((e117 (! (ite e86 e73 e70) :named term117)))
(let ((e118 (! (and e112 e105) :named term118)))
(let ((e119 (! (or e36 e99) :named term119)))
(let ((e120 (! (or e102 e79) :named term120)))
(let ((e121 (! (or e19 e98) :named term121)))
(let ((e122 (! (not e37) :named term122)))
(let ((e123 (! (not e103) :named term123)))
(let ((e124 (! (xor e88 e111) :named term124)))
(let ((e125 (! (= e25 e26) :named term125)))
(let ((e126 (! (=> e97 e97) :named term126)))
(let ((e127 (! (xor e20 e35) :named term127)))
(let ((e128 (! (=> e71 e115) :named term128)))
(let ((e129 (! (not e23) :named term129)))
(let ((e130 (! (=> e21 e38) :named term130)))
(let ((e131 (! (not e31) :named term131)))
(let ((e132 (! (not e119) :named term132)))
(let ((e133 (! (ite e80 e108 e125) :named term133)))
(let ((e134 (! (= e133 e72) :named term134)))
(let ((e135 (! (or e101 e84) :named term135)))
(let ((e136 (! (and e117 e33) :named term136)))
(let ((e137 (! (xor e30 e127) :named term137)))
(let ((e138 (! (xor e106 e122) :named term138)))
(let ((e139 (! (not e137) :named term139)))
(let ((e140 (! (xor e123 e90) :named term140)))
(let ((e141 (! (ite e114 e96 e138) :named term141)))
(let ((e142 (! (ite e78 e87 e27) :named term142)))
(let ((e143 (! (xor e124 e29) :named term143)))
(let ((e144 (! (not e93) :named term144)))
(let ((e145 (! (or e24 e22) :named term145)))
(let ((e146 (! (=> e76 e120) :named term146)))
(let ((e147 (! (= e28 e129) :named term147)))
(let ((e148 (! (ite e113 e130 e132) :named term148)))
(let ((e149 (! (or e109 e100) :named term149)))
(let ((e150 (! (not e141) :named term150)))
(let ((e151 (! (xor e116 e39) :named term151)))
(let ((e152 (! (not e131) :named term152)))
(let ((e153 (! (and e135 e140) :named term153)))
(let ((e154 (! (= e69 e149) :named term154)))
(let ((e155 (! (or e75 e85) :named term155)))
(let ((e156 (! (=> e92 e150) :named term156)))
(let ((e157 (! (ite e32 e143 e144) :named term157)))
(let ((e158 (! (= e154 e156) :named term158)))
(let ((e159 (! (and e146 e155) :named term159)))
(let ((e160 (! (and e159 e91) :named term160)))
(let ((e161 (! (xor e134 e134) :named term161)))
(let ((e162 (! (ite e148 e34 e136) :named term162)))
(let ((e163 (! (=> e157 e158) :named term163)))
(let ((e164 (! (=> e82 e153) :named term164)))
(let ((e165 (! (= e107 e160) :named term165)))
(let ((e166 (! (ite e81 e161 e151) :named term166)))
(let ((e167 (! (=> e95 e74) :named term167)))
(let ((e168 (! (xor e152 e147) :named term168)))
(let ((e169 (! (=> e128 e110) :named term169)))
(let ((e170 (! (ite e162 e167 e169) :named term170)))
(let ((e171 (! (=> e118 e142) :named term171)))
(let ((e172 (! (and e145 e166) :named term172)))
(let ((e173 (! (or e170 e171) :named term173)))
(let ((e174 (! (or e126 e172) :named term174)))
(let ((e175 (! (or e163 e173) :named term175)))
(let ((e176 (! (not e77) :named term176)))
(let ((e177 (! (not e174) :named term177)))
(let ((e178 (! (xor e165 e176) :named term178)))
(let ((e179 (! (ite e164 e168 e168) :named term179)))
(let ((e180 (! (and e139 e175) :named term180)))
(let ((e181 (! (and e177 e121) :named term181)))
(let ((e182 (! (ite e181 e180 e178) :named term182)))
(let ((e183 (! (=> e179 e182) :named term183)))
e183
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
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
(get-value (term160))
(get-value (term161))
(get-value (term162))
(get-value (term163))
(get-value (term164))
(get-value (term165))
(get-value (term166))
(get-value (term167))
(get-value (term168))
(get-value (term169))
(get-value (term170))
(get-value (term171))
(get-value (term172))
(get-value (term173))
(get-value (term174))
(get-value (term175))
(get-value (term176))
(get-value (term177))
(get-value (term178))
(get-value (term179))
(get-value (term180))
(get-value (term181))
(get-value (term182))
(get-value (term183))
(get-info :all-statistics)
