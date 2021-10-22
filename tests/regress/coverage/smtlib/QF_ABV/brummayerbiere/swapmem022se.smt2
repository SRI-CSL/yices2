(set-logic QF_ABV)
(set-info :source |
We swap two byte sequences of length 22 twice in memory.
The sequences can overlap, hence it is not always the case
that swapping them twice yields the initial memory.

Swapping is done via XOR in the following way:
x ^= y;
y ^= x;
x ^= y;

Contributed by Robert Brummayer (robert.brummayer@gmail.com).
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun start1 () (_ BitVec 32))
(declare-fun start2 () (_ BitVec 32))
(assert (let ((?v_0 (select a1 start1)) (?v_1 (select a1 start2))) (let ((?v_2 (bvnot ?v_1))) (let ((?v_3 (bvand (bvnot (bvand (bvnot ?v_0) ?v_2)) (bvnot (bvand ?v_0 ?v_1))))) (let ((?v_4 (bvnot ?v_3))) (let ((?v_5 (bvand (bvnot (bvand ?v_2 ?v_4)) (bvnot (bvand ?v_1 ?v_3))))) (let ((?v_6 (store (store (store a1 start1 ?v_3) start2 ?v_5) start1 (bvand (bvnot (bvand ?v_4 (bvnot ?v_5))) (bvnot (bvand ?v_3 ?v_5))))) (?v_7 (bvadd start1 (_ bv1 32))) (?v_10 (bvadd start2 (_ bv1 32)))) (let ((?v_8 (select ?v_6 ?v_7)) (?v_9 (select ?v_6 ?v_10))) (let ((?v_11 (bvnot ?v_9))) (let ((?v_12 (bvand (bvnot (bvand (bvnot ?v_8) ?v_11)) (bvnot (bvand ?v_8 ?v_9))))) (let ((?v_13 (bvnot ?v_12))) (let ((?v_14 (bvand (bvnot (bvand ?v_11 ?v_13)) (bvnot (bvand ?v_9 ?v_12))))) (let ((?v_15 (store (store (store ?v_6 ?v_7 ?v_12) ?v_10 ?v_14) ?v_7 (bvand (bvnot (bvand ?v_13 (bvnot ?v_14))) (bvnot (bvand ?v_12 ?v_14))))) (?v_16 (bvadd (_ bv1 32) ?v_7)) (?v_19 (bvadd (_ bv1 32) ?v_10))) (let ((?v_17 (select ?v_15 ?v_16)) (?v_18 (select ?v_15 ?v_19))) (let ((?v_20 (bvnot ?v_18))) (let ((?v_21 (bvand (bvnot (bvand (bvnot ?v_17) ?v_20)) (bvnot (bvand ?v_17 ?v_18))))) (let ((?v_22 (bvnot ?v_21))) (let ((?v_23 (bvand (bvnot (bvand ?v_20 ?v_22)) (bvnot (bvand ?v_18 ?v_21))))) (let ((?v_24 (store (store (store ?v_15 ?v_16 ?v_21) ?v_19 ?v_23) ?v_16 (bvand (bvnot (bvand ?v_22 (bvnot ?v_23))) (bvnot (bvand ?v_21 ?v_23))))) (?v_25 (bvadd (_ bv1 32) ?v_16)) (?v_28 (bvadd (_ bv1 32) ?v_19))) (let ((?v_26 (select ?v_24 ?v_25)) (?v_27 (select ?v_24 ?v_28))) (let ((?v_29 (bvnot ?v_27))) (let ((?v_30 (bvand (bvnot (bvand (bvnot ?v_26) ?v_29)) (bvnot (bvand ?v_26 ?v_27))))) (let ((?v_31 (bvnot ?v_30))) (let ((?v_32 (bvand (bvnot (bvand ?v_29 ?v_31)) (bvnot (bvand ?v_27 ?v_30))))) (let ((?v_33 (store (store (store ?v_24 ?v_25 ?v_30) ?v_28 ?v_32) ?v_25 (bvand (bvnot (bvand ?v_31 (bvnot ?v_32))) (bvnot (bvand ?v_30 ?v_32))))) (?v_34 (bvadd (_ bv1 32) ?v_25)) (?v_37 (bvadd (_ bv1 32) ?v_28))) (let ((?v_35 (select ?v_33 ?v_34)) (?v_36 (select ?v_33 ?v_37))) (let ((?v_38 (bvnot ?v_36))) (let ((?v_39 (bvand (bvnot (bvand (bvnot ?v_35) ?v_38)) (bvnot (bvand ?v_35 ?v_36))))) (let ((?v_40 (bvnot ?v_39))) (let ((?v_41 (bvand (bvnot (bvand ?v_38 ?v_40)) (bvnot (bvand ?v_36 ?v_39))))) (let ((?v_42 (store (store (store ?v_33 ?v_34 ?v_39) ?v_37 ?v_41) ?v_34 (bvand (bvnot (bvand ?v_40 (bvnot ?v_41))) (bvnot (bvand ?v_39 ?v_41))))) (?v_43 (bvadd (_ bv1 32) ?v_34)) (?v_46 (bvadd (_ bv1 32) ?v_37))) (let ((?v_44 (select ?v_42 ?v_43)) (?v_45 (select ?v_42 ?v_46))) (let ((?v_47 (bvnot ?v_45))) (let ((?v_48 (bvand (bvnot (bvand (bvnot ?v_44) ?v_47)) (bvnot (bvand ?v_44 ?v_45))))) (let ((?v_49 (bvnot ?v_48))) (let ((?v_50 (bvand (bvnot (bvand ?v_47 ?v_49)) (bvnot (bvand ?v_45 ?v_48))))) (let ((?v_51 (store (store (store ?v_42 ?v_43 ?v_48) ?v_46 ?v_50) ?v_43 (bvand (bvnot (bvand ?v_49 (bvnot ?v_50))) (bvnot (bvand ?v_48 ?v_50))))) (?v_52 (bvadd (_ bv1 32) ?v_43)) (?v_55 (bvadd (_ bv1 32) ?v_46))) (let ((?v_53 (select ?v_51 ?v_52)) (?v_54 (select ?v_51 ?v_55))) (let ((?v_56 (bvnot ?v_54))) (let ((?v_57 (bvand (bvnot (bvand (bvnot ?v_53) ?v_56)) (bvnot (bvand ?v_53 ?v_54))))) (let ((?v_58 (bvnot ?v_57))) (let ((?v_59 (bvand (bvnot (bvand ?v_56 ?v_58)) (bvnot (bvand ?v_54 ?v_57))))) (let ((?v_60 (store (store (store ?v_51 ?v_52 ?v_57) ?v_55 ?v_59) ?v_52 (bvand (bvnot (bvand ?v_58 (bvnot ?v_59))) (bvnot (bvand ?v_57 ?v_59))))) (?v_61 (bvadd (_ bv1 32) ?v_52)) (?v_64 (bvadd (_ bv1 32) ?v_55))) (let ((?v_62 (select ?v_60 ?v_61)) (?v_63 (select ?v_60 ?v_64))) (let ((?v_65 (bvnot ?v_63))) (let ((?v_66 (bvand (bvnot (bvand (bvnot ?v_62) ?v_65)) (bvnot (bvand ?v_62 ?v_63))))) (let ((?v_67 (bvnot ?v_66))) (let ((?v_68 (bvand (bvnot (bvand ?v_65 ?v_67)) (bvnot (bvand ?v_63 ?v_66))))) (let ((?v_69 (store (store (store ?v_60 ?v_61 ?v_66) ?v_64 ?v_68) ?v_61 (bvand (bvnot (bvand ?v_67 (bvnot ?v_68))) (bvnot (bvand ?v_66 ?v_68))))) (?v_70 (bvadd (_ bv1 32) ?v_61)) (?v_73 (bvadd (_ bv1 32) ?v_64))) (let ((?v_71 (select ?v_69 ?v_70)) (?v_72 (select ?v_69 ?v_73))) (let ((?v_74 (bvnot ?v_72))) (let ((?v_75 (bvand (bvnot (bvand (bvnot ?v_71) ?v_74)) (bvnot (bvand ?v_71 ?v_72))))) (let ((?v_76 (bvnot ?v_75))) (let ((?v_77 (bvand (bvnot (bvand ?v_74 ?v_76)) (bvnot (bvand ?v_72 ?v_75))))) (let ((?v_78 (store (store (store ?v_69 ?v_70 ?v_75) ?v_73 ?v_77) ?v_70 (bvand (bvnot (bvand ?v_76 (bvnot ?v_77))) (bvnot (bvand ?v_75 ?v_77))))) (?v_79 (bvadd (_ bv1 32) ?v_70)) (?v_82 (bvadd (_ bv1 32) ?v_73))) (let ((?v_80 (select ?v_78 ?v_79)) (?v_81 (select ?v_78 ?v_82))) (let ((?v_83 (bvnot ?v_81))) (let ((?v_84 (bvand (bvnot (bvand (bvnot ?v_80) ?v_83)) (bvnot (bvand ?v_80 ?v_81))))) (let ((?v_85 (bvnot ?v_84))) (let ((?v_86 (bvand (bvnot (bvand ?v_83 ?v_85)) (bvnot (bvand ?v_81 ?v_84))))) (let ((?v_87 (store (store (store ?v_78 ?v_79 ?v_84) ?v_82 ?v_86) ?v_79 (bvand (bvnot (bvand ?v_85 (bvnot ?v_86))) (bvnot (bvand ?v_84 ?v_86))))) (?v_88 (bvadd (_ bv1 32) ?v_79)) (?v_91 (bvadd (_ bv1 32) ?v_82))) (let ((?v_89 (select ?v_87 ?v_88)) (?v_90 (select ?v_87 ?v_91))) (let ((?v_92 (bvnot ?v_90))) (let ((?v_93 (bvand (bvnot (bvand (bvnot ?v_89) ?v_92)) (bvnot (bvand ?v_89 ?v_90))))) (let ((?v_94 (bvnot ?v_93))) (let ((?v_95 (bvand (bvnot (bvand ?v_92 ?v_94)) (bvnot (bvand ?v_90 ?v_93))))) (let ((?v_96 (store (store (store ?v_87 ?v_88 ?v_93) ?v_91 ?v_95) ?v_88 (bvand (bvnot (bvand ?v_94 (bvnot ?v_95))) (bvnot (bvand ?v_93 ?v_95))))) (?v_97 (bvadd (_ bv1 32) ?v_88)) (?v_100 (bvadd (_ bv1 32) ?v_91))) (let ((?v_98 (select ?v_96 ?v_97)) (?v_99 (select ?v_96 ?v_100))) (let ((?v_101 (bvnot ?v_99))) (let ((?v_102 (bvand (bvnot (bvand (bvnot ?v_98) ?v_101)) (bvnot (bvand ?v_98 ?v_99))))) (let ((?v_103 (bvnot ?v_102))) (let ((?v_104 (bvand (bvnot (bvand ?v_101 ?v_103)) (bvnot (bvand ?v_99 ?v_102))))) (let ((?v_105 (store (store (store ?v_96 ?v_97 ?v_102) ?v_100 ?v_104) ?v_97 (bvand (bvnot (bvand ?v_103 (bvnot ?v_104))) (bvnot (bvand ?v_102 ?v_104))))) (?v_106 (bvadd (_ bv1 32) ?v_97)) (?v_109 (bvadd (_ bv1 32) ?v_100))) (let ((?v_107 (select ?v_105 ?v_106)) (?v_108 (select ?v_105 ?v_109))) (let ((?v_110 (bvnot ?v_108))) (let ((?v_111 (bvand (bvnot (bvand (bvnot ?v_107) ?v_110)) (bvnot (bvand ?v_107 ?v_108))))) (let ((?v_112 (bvnot ?v_111))) (let ((?v_113 (bvand (bvnot (bvand ?v_110 ?v_112)) (bvnot (bvand ?v_108 ?v_111))))) (let ((?v_114 (store (store (store ?v_105 ?v_106 ?v_111) ?v_109 ?v_113) ?v_106 (bvand (bvnot (bvand ?v_112 (bvnot ?v_113))) (bvnot (bvand ?v_111 ?v_113))))) (?v_115 (bvadd (_ bv1 32) ?v_106)) (?v_118 (bvadd (_ bv1 32) ?v_109))) (let ((?v_116 (select ?v_114 ?v_115)) (?v_117 (select ?v_114 ?v_118))) (let ((?v_119 (bvnot ?v_117))) (let ((?v_120 (bvand (bvnot (bvand (bvnot ?v_116) ?v_119)) (bvnot (bvand ?v_116 ?v_117))))) (let ((?v_121 (bvnot ?v_120))) (let ((?v_122 (bvand (bvnot (bvand ?v_119 ?v_121)) (bvnot (bvand ?v_117 ?v_120))))) (let ((?v_123 (store (store (store ?v_114 ?v_115 ?v_120) ?v_118 ?v_122) ?v_115 (bvand (bvnot (bvand ?v_121 (bvnot ?v_122))) (bvnot (bvand ?v_120 ?v_122))))) (?v_124 (bvadd (_ bv1 32) ?v_115)) (?v_127 (bvadd (_ bv1 32) ?v_118))) (let ((?v_125 (select ?v_123 ?v_124)) (?v_126 (select ?v_123 ?v_127))) (let ((?v_128 (bvnot ?v_126))) (let ((?v_129 (bvand (bvnot (bvand (bvnot ?v_125) ?v_128)) (bvnot (bvand ?v_125 ?v_126))))) (let ((?v_130 (bvnot ?v_129))) (let ((?v_131 (bvand (bvnot (bvand ?v_128 ?v_130)) (bvnot (bvand ?v_126 ?v_129))))) (let ((?v_132 (store (store (store ?v_123 ?v_124 ?v_129) ?v_127 ?v_131) ?v_124 (bvand (bvnot (bvand ?v_130 (bvnot ?v_131))) (bvnot (bvand ?v_129 ?v_131))))) (?v_133 (bvadd (_ bv1 32) ?v_124)) (?v_136 (bvadd (_ bv1 32) ?v_127))) (let ((?v_134 (select ?v_132 ?v_133)) (?v_135 (select ?v_132 ?v_136))) (let ((?v_137 (bvnot ?v_135))) (let ((?v_138 (bvand (bvnot (bvand (bvnot ?v_134) ?v_137)) (bvnot (bvand ?v_134 ?v_135))))) (let ((?v_139 (bvnot ?v_138))) (let ((?v_140 (bvand (bvnot (bvand ?v_137 ?v_139)) (bvnot (bvand ?v_135 ?v_138))))) (let ((?v_141 (store (store (store ?v_132 ?v_133 ?v_138) ?v_136 ?v_140) ?v_133 (bvand (bvnot (bvand ?v_139 (bvnot ?v_140))) (bvnot (bvand ?v_138 ?v_140))))) (?v_142 (bvadd (_ bv1 32) ?v_133)) (?v_145 (bvadd (_ bv1 32) ?v_136))) (let ((?v_143 (select ?v_141 ?v_142)) (?v_144 (select ?v_141 ?v_145))) (let ((?v_146 (bvnot ?v_144))) (let ((?v_147 (bvand (bvnot (bvand (bvnot ?v_143) ?v_146)) (bvnot (bvand ?v_143 ?v_144))))) (let ((?v_148 (bvnot ?v_147))) (let ((?v_149 (bvand (bvnot (bvand ?v_146 ?v_148)) (bvnot (bvand ?v_144 ?v_147))))) (let ((?v_150 (store (store (store ?v_141 ?v_142 ?v_147) ?v_145 ?v_149) ?v_142 (bvand (bvnot (bvand ?v_148 (bvnot ?v_149))) (bvnot (bvand ?v_147 ?v_149))))) (?v_151 (bvadd (_ bv1 32) ?v_142)) (?v_154 (bvadd (_ bv1 32) ?v_145))) (let ((?v_152 (select ?v_150 ?v_151)) (?v_153 (select ?v_150 ?v_154))) (let ((?v_155 (bvnot ?v_153))) (let ((?v_156 (bvand (bvnot (bvand (bvnot ?v_152) ?v_155)) (bvnot (bvand ?v_152 ?v_153))))) (let ((?v_157 (bvnot ?v_156))) (let ((?v_158 (bvand (bvnot (bvand ?v_155 ?v_157)) (bvnot (bvand ?v_153 ?v_156))))) (let ((?v_159 (store (store (store ?v_150 ?v_151 ?v_156) ?v_154 ?v_158) ?v_151 (bvand (bvnot (bvand ?v_157 (bvnot ?v_158))) (bvnot (bvand ?v_156 ?v_158))))) (?v_160 (bvadd (_ bv1 32) ?v_151)) (?v_163 (bvadd (_ bv1 32) ?v_154))) (let ((?v_161 (select ?v_159 ?v_160)) (?v_162 (select ?v_159 ?v_163))) (let ((?v_164 (bvnot ?v_162))) (let ((?v_165 (bvand (bvnot (bvand (bvnot ?v_161) ?v_164)) (bvnot (bvand ?v_161 ?v_162))))) (let ((?v_166 (bvnot ?v_165))) (let ((?v_167 (bvand (bvnot (bvand ?v_164 ?v_166)) (bvnot (bvand ?v_162 ?v_165))))) (let ((?v_168 (store (store (store ?v_159 ?v_160 ?v_165) ?v_163 ?v_167) ?v_160 (bvand (bvnot (bvand ?v_166 (bvnot ?v_167))) (bvnot (bvand ?v_165 ?v_167))))) (?v_169 (bvadd (_ bv1 32) ?v_160)) (?v_172 (bvadd (_ bv1 32) ?v_163))) (let ((?v_170 (select ?v_168 ?v_169)) (?v_171 (select ?v_168 ?v_172))) (let ((?v_173 (bvnot ?v_171))) (let ((?v_174 (bvand (bvnot (bvand (bvnot ?v_170) ?v_173)) (bvnot (bvand ?v_170 ?v_171))))) (let ((?v_175 (bvnot ?v_174))) (let ((?v_176 (bvand (bvnot (bvand ?v_173 ?v_175)) (bvnot (bvand ?v_171 ?v_174))))) (let ((?v_177 (store (store (store ?v_168 ?v_169 ?v_174) ?v_172 ?v_176) ?v_169 (bvand (bvnot (bvand ?v_175 (bvnot ?v_176))) (bvnot (bvand ?v_174 ?v_176))))) (?v_178 (bvadd (_ bv1 32) ?v_169)) (?v_181 (bvadd (_ bv1 32) ?v_172))) (let ((?v_179 (select ?v_177 ?v_178)) (?v_180 (select ?v_177 ?v_181))) (let ((?v_182 (bvnot ?v_180))) (let ((?v_183 (bvand (bvnot (bvand (bvnot ?v_179) ?v_182)) (bvnot (bvand ?v_179 ?v_180))))) (let ((?v_184 (bvnot ?v_183))) (let ((?v_185 (bvand (bvnot (bvand ?v_182 ?v_184)) (bvnot (bvand ?v_180 ?v_183))))) (let ((?v_186 (store (store (store ?v_177 ?v_178 ?v_183) ?v_181 ?v_185) ?v_178 (bvand (bvnot (bvand ?v_184 (bvnot ?v_185))) (bvnot (bvand ?v_183 ?v_185))))) (?v_187 (bvadd (_ bv1 32) ?v_178)) (?v_190 (bvadd (_ bv1 32) ?v_181))) (let ((?v_188 (select ?v_186 ?v_187)) (?v_189 (select ?v_186 ?v_190))) (let ((?v_191 (bvnot ?v_189))) (let ((?v_192 (bvand (bvnot (bvand (bvnot ?v_188) ?v_191)) (bvnot (bvand ?v_188 ?v_189))))) (let ((?v_193 (bvnot ?v_192))) (let ((?v_194 (bvand (bvnot (bvand ?v_191 ?v_193)) (bvnot (bvand ?v_189 ?v_192))))) (let ((?v_195 (store (store (store ?v_186 ?v_187 ?v_192) ?v_190 ?v_194) ?v_187 (bvand (bvnot (bvand ?v_193 (bvnot ?v_194))) (bvnot (bvand ?v_192 ?v_194)))))) (let ((?v_196 (select ?v_195 start1)) (?v_197 (select ?v_195 start2))) (let ((?v_198 (bvnot ?v_197))) (let ((?v_199 (bvand (bvnot (bvand (bvnot ?v_196) ?v_198)) (bvnot (bvand ?v_196 ?v_197))))) (let ((?v_200 (bvnot ?v_199))) (let ((?v_201 (bvand (bvnot (bvand ?v_198 ?v_200)) (bvnot (bvand ?v_197 ?v_199))))) (let ((?v_202 (store (store (store ?v_195 start1 ?v_199) start2 ?v_201) start1 (bvand (bvnot (bvand ?v_200 (bvnot ?v_201))) (bvnot (bvand ?v_199 ?v_201)))))) (let ((?v_203 (select ?v_202 ?v_7)) (?v_204 (select ?v_202 ?v_10))) (let ((?v_205 (bvnot ?v_204))) (let ((?v_206 (bvand (bvnot (bvand (bvnot ?v_203) ?v_205)) (bvnot (bvand ?v_203 ?v_204))))) (let ((?v_207 (bvnot ?v_206))) (let ((?v_208 (bvand (bvnot (bvand ?v_205 ?v_207)) (bvnot (bvand ?v_204 ?v_206))))) (let ((?v_209 (store (store (store ?v_202 ?v_7 ?v_206) ?v_10 ?v_208) ?v_7 (bvand (bvnot (bvand ?v_207 (bvnot ?v_208))) (bvnot (bvand ?v_206 ?v_208)))))) (let ((?v_210 (select ?v_209 ?v_16)) (?v_211 (select ?v_209 ?v_19))) (let ((?v_212 (bvnot ?v_211))) (let ((?v_213 (bvand (bvnot (bvand (bvnot ?v_210) ?v_212)) (bvnot (bvand ?v_210 ?v_211))))) (let ((?v_214 (bvnot ?v_213))) (let ((?v_215 (bvand (bvnot (bvand ?v_212 ?v_214)) (bvnot (bvand ?v_211 ?v_213))))) (let ((?v_216 (store (store (store ?v_209 ?v_16 ?v_213) ?v_19 ?v_215) ?v_16 (bvand (bvnot (bvand ?v_214 (bvnot ?v_215))) (bvnot (bvand ?v_213 ?v_215)))))) (let ((?v_217 (select ?v_216 ?v_25)) (?v_218 (select ?v_216 ?v_28))) (let ((?v_219 (bvnot ?v_218))) (let ((?v_220 (bvand (bvnot (bvand (bvnot ?v_217) ?v_219)) (bvnot (bvand ?v_217 ?v_218))))) (let ((?v_221 (bvnot ?v_220))) (let ((?v_222 (bvand (bvnot (bvand ?v_219 ?v_221)) (bvnot (bvand ?v_218 ?v_220))))) (let ((?v_223 (store (store (store ?v_216 ?v_25 ?v_220) ?v_28 ?v_222) ?v_25 (bvand (bvnot (bvand ?v_221 (bvnot ?v_222))) (bvnot (bvand ?v_220 ?v_222)))))) (let ((?v_224 (select ?v_223 ?v_34)) (?v_225 (select ?v_223 ?v_37))) (let ((?v_226 (bvnot ?v_225))) (let ((?v_227 (bvand (bvnot (bvand (bvnot ?v_224) ?v_226)) (bvnot (bvand ?v_224 ?v_225))))) (let ((?v_228 (bvnot ?v_227))) (let ((?v_229 (bvand (bvnot (bvand ?v_226 ?v_228)) (bvnot (bvand ?v_225 ?v_227))))) (let ((?v_230 (store (store (store ?v_223 ?v_34 ?v_227) ?v_37 ?v_229) ?v_34 (bvand (bvnot (bvand ?v_228 (bvnot ?v_229))) (bvnot (bvand ?v_227 ?v_229)))))) (let ((?v_231 (select ?v_230 ?v_43)) (?v_232 (select ?v_230 ?v_46))) (let ((?v_233 (bvnot ?v_232))) (let ((?v_234 (bvand (bvnot (bvand (bvnot ?v_231) ?v_233)) (bvnot (bvand ?v_231 ?v_232))))) (let ((?v_235 (bvnot ?v_234))) (let ((?v_236 (bvand (bvnot (bvand ?v_233 ?v_235)) (bvnot (bvand ?v_232 ?v_234))))) (let ((?v_237 (store (store (store ?v_230 ?v_43 ?v_234) ?v_46 ?v_236) ?v_43 (bvand (bvnot (bvand ?v_235 (bvnot ?v_236))) (bvnot (bvand ?v_234 ?v_236)))))) (let ((?v_238 (select ?v_237 ?v_52)) (?v_239 (select ?v_237 ?v_55))) (let ((?v_240 (bvnot ?v_239))) (let ((?v_241 (bvand (bvnot (bvand (bvnot ?v_238) ?v_240)) (bvnot (bvand ?v_238 ?v_239))))) (let ((?v_242 (bvnot ?v_241))) (let ((?v_243 (bvand (bvnot (bvand ?v_240 ?v_242)) (bvnot (bvand ?v_239 ?v_241))))) (let ((?v_244 (store (store (store ?v_237 ?v_52 ?v_241) ?v_55 ?v_243) ?v_52 (bvand (bvnot (bvand ?v_242 (bvnot ?v_243))) (bvnot (bvand ?v_241 ?v_243)))))) (let ((?v_245 (select ?v_244 ?v_61)) (?v_246 (select ?v_244 ?v_64))) (let ((?v_247 (bvnot ?v_246))) (let ((?v_248 (bvand (bvnot (bvand (bvnot ?v_245) ?v_247)) (bvnot (bvand ?v_245 ?v_246))))) (let ((?v_249 (bvnot ?v_248))) (let ((?v_250 (bvand (bvnot (bvand ?v_247 ?v_249)) (bvnot (bvand ?v_246 ?v_248))))) (let ((?v_251 (store (store (store ?v_244 ?v_61 ?v_248) ?v_64 ?v_250) ?v_61 (bvand (bvnot (bvand ?v_249 (bvnot ?v_250))) (bvnot (bvand ?v_248 ?v_250)))))) (let ((?v_252 (select ?v_251 ?v_70)) (?v_253 (select ?v_251 ?v_73))) (let ((?v_254 (bvnot ?v_253))) (let ((?v_255 (bvand (bvnot (bvand (bvnot ?v_252) ?v_254)) (bvnot (bvand ?v_252 ?v_253))))) (let ((?v_256 (bvnot ?v_255))) (let ((?v_257 (bvand (bvnot (bvand ?v_254 ?v_256)) (bvnot (bvand ?v_253 ?v_255))))) (let ((?v_258 (store (store (store ?v_251 ?v_70 ?v_255) ?v_73 ?v_257) ?v_70 (bvand (bvnot (bvand ?v_256 (bvnot ?v_257))) (bvnot (bvand ?v_255 ?v_257)))))) (let ((?v_259 (select ?v_258 ?v_79)) (?v_260 (select ?v_258 ?v_82))) (let ((?v_261 (bvnot ?v_260))) (let ((?v_262 (bvand (bvnot (bvand (bvnot ?v_259) ?v_261)) (bvnot (bvand ?v_259 ?v_260))))) (let ((?v_263 (bvnot ?v_262))) (let ((?v_264 (bvand (bvnot (bvand ?v_261 ?v_263)) (bvnot (bvand ?v_260 ?v_262))))) (let ((?v_265 (store (store (store ?v_258 ?v_79 ?v_262) ?v_82 ?v_264) ?v_79 (bvand (bvnot (bvand ?v_263 (bvnot ?v_264))) (bvnot (bvand ?v_262 ?v_264)))))) (let ((?v_266 (select ?v_265 ?v_88)) (?v_267 (select ?v_265 ?v_91))) (let ((?v_268 (bvnot ?v_267))) (let ((?v_269 (bvand (bvnot (bvand (bvnot ?v_266) ?v_268)) (bvnot (bvand ?v_266 ?v_267))))) (let ((?v_270 (bvnot ?v_269))) (let ((?v_271 (bvand (bvnot (bvand ?v_268 ?v_270)) (bvnot (bvand ?v_267 ?v_269))))) (let ((?v_272 (store (store (store ?v_265 ?v_88 ?v_269) ?v_91 ?v_271) ?v_88 (bvand (bvnot (bvand ?v_270 (bvnot ?v_271))) (bvnot (bvand ?v_269 ?v_271)))))) (let ((?v_273 (select ?v_272 ?v_97)) (?v_274 (select ?v_272 ?v_100))) (let ((?v_275 (bvnot ?v_274))) (let ((?v_276 (bvand (bvnot (bvand (bvnot ?v_273) ?v_275)) (bvnot (bvand ?v_273 ?v_274))))) (let ((?v_277 (bvnot ?v_276))) (let ((?v_278 (bvand (bvnot (bvand ?v_275 ?v_277)) (bvnot (bvand ?v_274 ?v_276))))) (let ((?v_279 (store (store (store ?v_272 ?v_97 ?v_276) ?v_100 ?v_278) ?v_97 (bvand (bvnot (bvand ?v_277 (bvnot ?v_278))) (bvnot (bvand ?v_276 ?v_278)))))) (let ((?v_280 (select ?v_279 ?v_106)) (?v_281 (select ?v_279 ?v_109))) (let ((?v_282 (bvnot ?v_281))) (let ((?v_283 (bvand (bvnot (bvand (bvnot ?v_280) ?v_282)) (bvnot (bvand ?v_280 ?v_281))))) (let ((?v_284 (bvnot ?v_283))) (let ((?v_285 (bvand (bvnot (bvand ?v_282 ?v_284)) (bvnot (bvand ?v_281 ?v_283))))) (let ((?v_286 (store (store (store ?v_279 ?v_106 ?v_283) ?v_109 ?v_285) ?v_106 (bvand (bvnot (bvand ?v_284 (bvnot ?v_285))) (bvnot (bvand ?v_283 ?v_285)))))) (let ((?v_287 (select ?v_286 ?v_115)) (?v_288 (select ?v_286 ?v_118))) (let ((?v_289 (bvnot ?v_288))) (let ((?v_290 (bvand (bvnot (bvand (bvnot ?v_287) ?v_289)) (bvnot (bvand ?v_287 ?v_288))))) (let ((?v_291 (bvnot ?v_290))) (let ((?v_292 (bvand (bvnot (bvand ?v_289 ?v_291)) (bvnot (bvand ?v_288 ?v_290))))) (let ((?v_293 (store (store (store ?v_286 ?v_115 ?v_290) ?v_118 ?v_292) ?v_115 (bvand (bvnot (bvand ?v_291 (bvnot ?v_292))) (bvnot (bvand ?v_290 ?v_292)))))) (let ((?v_294 (select ?v_293 ?v_124)) (?v_295 (select ?v_293 ?v_127))) (let ((?v_296 (bvnot ?v_295))) (let ((?v_297 (bvand (bvnot (bvand (bvnot ?v_294) ?v_296)) (bvnot (bvand ?v_294 ?v_295))))) (let ((?v_298 (bvnot ?v_297))) (let ((?v_299 (bvand (bvnot (bvand ?v_296 ?v_298)) (bvnot (bvand ?v_295 ?v_297))))) (let ((?v_300 (store (store (store ?v_293 ?v_124 ?v_297) ?v_127 ?v_299) ?v_124 (bvand (bvnot (bvand ?v_298 (bvnot ?v_299))) (bvnot (bvand ?v_297 ?v_299)))))) (let ((?v_301 (select ?v_300 ?v_133)) (?v_302 (select ?v_300 ?v_136))) (let ((?v_303 (bvnot ?v_302))) (let ((?v_304 (bvand (bvnot (bvand (bvnot ?v_301) ?v_303)) (bvnot (bvand ?v_301 ?v_302))))) (let ((?v_305 (bvnot ?v_304))) (let ((?v_306 (bvand (bvnot (bvand ?v_303 ?v_305)) (bvnot (bvand ?v_302 ?v_304))))) (let ((?v_307 (store (store (store ?v_300 ?v_133 ?v_304) ?v_136 ?v_306) ?v_133 (bvand (bvnot (bvand ?v_305 (bvnot ?v_306))) (bvnot (bvand ?v_304 ?v_306)))))) (let ((?v_308 (select ?v_307 ?v_142)) (?v_309 (select ?v_307 ?v_145))) (let ((?v_310 (bvnot ?v_309))) (let ((?v_311 (bvand (bvnot (bvand (bvnot ?v_308) ?v_310)) (bvnot (bvand ?v_308 ?v_309))))) (let ((?v_312 (bvnot ?v_311))) (let ((?v_313 (bvand (bvnot (bvand ?v_310 ?v_312)) (bvnot (bvand ?v_309 ?v_311))))) (let ((?v_314 (store (store (store ?v_307 ?v_142 ?v_311) ?v_145 ?v_313) ?v_142 (bvand (bvnot (bvand ?v_312 (bvnot ?v_313))) (bvnot (bvand ?v_311 ?v_313)))))) (let ((?v_315 (select ?v_314 ?v_151)) (?v_316 (select ?v_314 ?v_154))) (let ((?v_317 (bvnot ?v_316))) (let ((?v_318 (bvand (bvnot (bvand (bvnot ?v_315) ?v_317)) (bvnot (bvand ?v_315 ?v_316))))) (let ((?v_319 (bvnot ?v_318))) (let ((?v_320 (bvand (bvnot (bvand ?v_317 ?v_319)) (bvnot (bvand ?v_316 ?v_318))))) (let ((?v_321 (store (store (store ?v_314 ?v_151 ?v_318) ?v_154 ?v_320) ?v_151 (bvand (bvnot (bvand ?v_319 (bvnot ?v_320))) (bvnot (bvand ?v_318 ?v_320)))))) (let ((?v_322 (select ?v_321 ?v_160)) (?v_323 (select ?v_321 ?v_163))) (let ((?v_324 (bvnot ?v_323))) (let ((?v_325 (bvand (bvnot (bvand (bvnot ?v_322) ?v_324)) (bvnot (bvand ?v_322 ?v_323))))) (let ((?v_326 (bvnot ?v_325))) (let ((?v_327 (bvand (bvnot (bvand ?v_324 ?v_326)) (bvnot (bvand ?v_323 ?v_325))))) (let ((?v_328 (store (store (store ?v_321 ?v_160 ?v_325) ?v_163 ?v_327) ?v_160 (bvand (bvnot (bvand ?v_326 (bvnot ?v_327))) (bvnot (bvand ?v_325 ?v_327)))))) (let ((?v_329 (select ?v_328 ?v_169)) (?v_330 (select ?v_328 ?v_172))) (let ((?v_331 (bvnot ?v_330))) (let ((?v_332 (bvand (bvnot (bvand (bvnot ?v_329) ?v_331)) (bvnot (bvand ?v_329 ?v_330))))) (let ((?v_333 (bvnot ?v_332))) (let ((?v_334 (bvand (bvnot (bvand ?v_331 ?v_333)) (bvnot (bvand ?v_330 ?v_332))))) (let ((?v_335 (store (store (store ?v_328 ?v_169 ?v_332) ?v_172 ?v_334) ?v_169 (bvand (bvnot (bvand ?v_333 (bvnot ?v_334))) (bvnot (bvand ?v_332 ?v_334)))))) (let ((?v_336 (select ?v_335 ?v_178)) (?v_337 (select ?v_335 ?v_181))) (let ((?v_338 (bvnot ?v_337))) (let ((?v_339 (bvand (bvnot (bvand (bvnot ?v_336) ?v_338)) (bvnot (bvand ?v_336 ?v_337))))) (let ((?v_340 (bvnot ?v_339))) (let ((?v_341 (bvand (bvnot (bvand ?v_338 ?v_340)) (bvnot (bvand ?v_337 ?v_339))))) (let ((?v_342 (store (store (store ?v_335 ?v_178 ?v_339) ?v_181 ?v_341) ?v_178 (bvand (bvnot (bvand ?v_340 (bvnot ?v_341))) (bvnot (bvand ?v_339 ?v_341)))))) (let ((?v_343 (select ?v_342 ?v_187)) (?v_344 (select ?v_342 ?v_190))) (let ((?v_345 (bvnot ?v_344))) (let ((?v_346 (bvand (bvnot (bvand (bvnot ?v_343) ?v_345)) (bvnot (bvand ?v_343 ?v_344))))) (let ((?v_347 (bvnot ?v_346))) (let ((?v_348 (bvand (bvnot (bvand ?v_345 ?v_347)) (bvnot (bvand ?v_344 ?v_346))))) (not (= (bvnot (ite (= a1 (store (store (store ?v_342 ?v_187 ?v_346) ?v_190 ?v_348) ?v_187 (bvand (bvnot (bvand ?v_347 (bvnot ?v_348))) (bvnot (bvand ?v_346 ?v_348))))) (_ bv1 1) (_ bv0 1))) (_ bv0 1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
(exit)
