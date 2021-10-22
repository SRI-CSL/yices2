(set-logic QF_LIA)
(set-info :source |
Mathsat benchmarks available from http://mathsat.itc.it

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun DUMMY_PWR_6 () Bool)
(declare-fun DUMMY_PWR_3 () Bool)
(declare-fun ENABLE_6 () Bool)
(declare-fun RESTART_16 () Bool)
(declare-fun stato_reg_19 () Int)
(declare-fun ENABLE_19 () Bool)
(declare-fun AVERAGE_9 () Bool)
(declare-fun Reg1_Reg_19 () Int)
(declare-fun ENABLE_7 () Bool)
(declare-fun AVERAGE_16 () Bool)
(declare-fun Reg2_Reg_19 () Int)
(declare-fun DATA_IN_3 () Int)
(declare-fun Reg3_Reg_19 () Int)
(declare-fun Reg4_Reg_19 () Int)
(declare-fun ENABLE_4 () Bool)
(declare-fun RESTART_5 () Bool)
(declare-fun RESTART_4 () Bool)
(declare-fun DATA_IN_17 () Int)
(declare-fun DUMMY_PWR_19 () Bool)
(declare-fun DUMMY_PWR_13 () Bool)
(declare-fun DATA_IN_13 () Int)
(declare-fun RESTART_3 () Bool)
(declare-fun ENABLE_2 () Bool)
(declare-fun AVERAGE_6 () Bool)
(declare-fun DUMMY_PWR_11 () Bool)
(declare-fun DATA_IN_11 () Int)
(declare-fun ENABLE_3 () Bool)
(declare-fun DUMMY_PWR_5 () Bool)
(declare-fun AVERAGE_8 () Bool)
(declare-fun RESTART_15 () Bool)
(declare-fun AVERAGE_13 () Bool)
(declare-fun Rmax_Reg_19 () Int)
(declare-fun ENABLE_11 () Bool)
(declare-fun DUMMY_PWR_2 () Bool)
(declare-fun DUMMY_PWR_15 () Bool)
(declare-fun DATA_IN_10 () Int)
(declare-fun DUMMY_PWR_12 () Bool)
(declare-fun AVERAGE_15 () Bool)
(declare-fun DATA_IN_4 () Int)
(declare-fun ENABLE_12 () Bool)
(declare-fun RESTART_7 () Bool)
(declare-fun DATA_IN_19 () Int)
(declare-fun RESTART_13 () Bool)
(declare-fun DATA_IN_6 () Int)
(declare-fun ENABLE_10 () Bool)
(declare-fun AVERAGE_2 () Bool)
(declare-fun ENABLE_13 () Bool)
(declare-fun DUMMY_PWR_9 () Bool)
(declare-fun RESTART_2 () Bool)
(declare-fun Rlast_Reg_19 () Int)
(declare-fun AVERAGE_11 () Bool)
(declare-fun DATA_IN_18 () Int)
(declare-fun DATA_IN_12 () Int)
(declare-fun RESTART_18 () Bool)
(declare-fun RESTART_6 () Bool)
(declare-fun RESTART_9 () Bool)
(declare-fun ENABLE_5 () Bool)
(declare-fun RESTART_1 () Bool)
(declare-fun RESTART_11 () Bool)
(declare-fun DUMMY_PWR_4 () Bool)
(declare-fun DATA_IN_5 () Int)
(declare-fun AVERAGE_18 () Bool)
(declare-fun RESTART_12 () Bool)
(declare-fun DATA_IN_15 () Int)
(declare-fun DATA_IN_14 () Int)
(declare-fun ENABLE_16 () Bool)
(declare-fun ENABLE_8 () Bool)
(declare-fun DATA_IN_8 () Int)
(declare-fun DUMMY_PWR_7 () Bool)
(declare-fun AVERAGE_12 () Bool)
(declare-fun RESTART_10 () Bool)
(declare-fun DATA_OUT_19 () Int)
(declare-fun AVERAGE_3 () Bool)
(declare-fun RESTART_14 () Bool)
(declare-fun DUMMY_PWR_17 () Bool)
(declare-fun RESTART_19 () Bool)
(declare-fun ENABLE_18 () Bool)
(declare-fun AVERAGE_19 () Bool)
(declare-fun ENABLE_9 () Bool)
(declare-fun RESTART_17 () Bool)
(declare-fun DUMMY_PWR_18 () Bool)
(declare-fun DATA_IN_2 () Int)
(declare-fun ENABLE_14 () Bool)
(declare-fun DUMMY_PWR_10 () Bool)
(declare-fun AVERAGE_10 () Bool)
(declare-fun AVERAGE_17 () Bool)
(declare-fun RESTART_8 () Bool)
(declare-fun Rmin_Reg_19 () Int)
(declare-fun DUMMY_PWR_8 () Bool)
(declare-fun DUMMY_PWR_16 () Bool)
(declare-fun AVERAGE_1 () Bool)
(declare-fun ENABLE_1 () Bool)
(declare-fun ENABLE_15 () Bool)
(declare-fun DATA_IN_16 () Int)
(declare-fun AVERAGE_5 () Bool)
(declare-fun AVERAGE_4 () Bool)
(declare-fun ENABLE_17 () Bool)
(declare-fun AVERAGE_14 () Bool)
(declare-fun AVERAGE_7 () Bool)
(declare-fun DUMMY_PWR_14 () Bool)
(declare-fun DATA_IN_7 () Int)
(declare-fun DATA_IN_1 () Int)
(declare-fun DATA_IN_9 () Int)
(assert (let ((?v_71 (= stato_reg_19 2)) (?v_72 (= stato_reg_19 1)) (?v_87 (ite (and DUMMY_PWR_10 (ite DUMMY_PWR_10 false true)) false true)) (?v_89 (ite (and DUMMY_PWR_11 (ite DUMMY_PWR_11 false true)) false true)) (?v_77 (ite (and DUMMY_PWR_5 (ite DUMMY_PWR_5 false true)) false true)) (?v_81 (ite (and DUMMY_PWR_7 (ite DUMMY_PWR_7 false true)) false true)) (?v_76 (ite (and DUMMY_PWR_4 (ite DUMMY_PWR_4 false true)) false true)) (?v_105 (ite (and DUMMY_PWR_19 (ite DUMMY_PWR_19 false true)) false true)) (?v_79 (ite (and DUMMY_PWR_6 (ite DUMMY_PWR_6 false true)) false true)) (?v_93 (ite (and DUMMY_PWR_13 (ite DUMMY_PWR_13 false true)) false true)) (?v_103 (ite (and DUMMY_PWR_18 (ite DUMMY_PWR_18 false true)) false true)) (?v_75 (ite (and DUMMY_PWR_3 (ite DUMMY_PWR_3 false true)) false true)) (?v_99 (ite (and DUMMY_PWR_16 (ite DUMMY_PWR_16 false true)) false true)) (?v_83 (ite (and DUMMY_PWR_8 (ite DUMMY_PWR_8 false true)) false true)) (?v_91 (ite (and DUMMY_PWR_12 (ite DUMMY_PWR_12 false true)) false true)) (?v_95 (ite (and DUMMY_PWR_14 (ite DUMMY_PWR_14 false true)) false true)) (?v_74 (ite (and DUMMY_PWR_2 (ite DUMMY_PWR_2 false true)) false true)) (?v_101 (ite (and DUMMY_PWR_17 (ite DUMMY_PWR_17 false true)) false true)) (?v_85 (ite (and DUMMY_PWR_9 (ite DUMMY_PWR_9 false true)) false true)) (?v_97 (ite (and DUMMY_PWR_15 (ite DUMMY_PWR_15 false true)) false true))) (let ((?v_0 (ite (or ?v_72 ?v_71) 2 1)) (?v_276 (or ?v_72 (and ?v_71 (and (ite RESTART_19 false true) (ite (and ENABLE_19 AVERAGE_19) false true))))) (?v_277 (and ?v_71 (or RESTART_19 (and ENABLE_19 (ite AVERAGE_19 false true))))) (?v_73 (and ?v_105 ?v_72)) (?v_135 (and ?v_105 ?v_71))) (let ((?v_171 (ite ?v_73 0 Reg3_Reg_19)) (?v_174 (ite (or ?v_72 (and ?v_71 (> DATA_IN_19 Rmax_Reg_19))) DATA_IN_19 Rmax_Reg_19)) (?v_153 (ite ?v_73 0 Reg2_Reg_19)) (?v_136 (ite ?v_73 0 Reg1_Reg_19)) (?v_191 (ite (or ?v_72 (and ?v_71 (> Rmin_Reg_19 DATA_IN_19))) DATA_IN_19 Rmin_Reg_19))) (let ((?v_274 (ite ?v_135 ?v_171 (ite ?v_73 0 Reg4_Reg_19))) (?v_106 (ite ?v_73 0 DATA_IN_19))) (let ((?v_273 (ite (and ?v_71 ENABLE_19) ?v_106 (ite ?v_73 0 Rlast_Reg_19))) (?v_68 (= ?v_0 2)) (?v_69 (= ?v_0 1))) (let ((?v_275 (and ?v_68 (or RESTART_18 (and ENABLE_18 (ite AVERAGE_18 false true))))) (?v_133 (and ?v_103 ?v_68)) (?v_70 (and ?v_103 ?v_69))) (let ((?v_134 (ite ?v_70 0 (ite ?v_135 ?v_106 ?v_136))) (?v_152 (ite ?v_70 0 (ite ?v_135 ?v_136 ?v_153))) (?v_170 (ite ?v_70 0 (ite ?v_135 ?v_153 ?v_171))) (?v_272 (or ?v_69 (and ?v_68 (and (ite RESTART_18 false true) (ite (and ENABLE_18 AVERAGE_18) false true))))) (?v_1 (ite (or ?v_69 ?v_68) 2 1)) (?v_175 (ite (or ?v_69 (and ?v_68 (> DATA_IN_18 ?v_174))) DATA_IN_18 ?v_174))) (let ((?v_270 (ite ?v_133 ?v_170 (ite ?v_70 0 ?v_274))) (?v_104 (ite ?v_70 0 DATA_IN_18))) (let ((?v_269 (ite (and ?v_68 ENABLE_18) ?v_104 (ite ?v_70 0 ?v_273))) (?v_192 (ite (or ?v_69 (and ?v_68 (> ?v_191 DATA_IN_18))) DATA_IN_18 ?v_191)) (?v_66 (= ?v_1 1)) (?v_65 (= ?v_1 2))) (let ((?v_67 (and ?v_101 ?v_66)) (?v_131 (and ?v_101 ?v_65)) (?v_271 (and ?v_65 (or RESTART_17 (and ENABLE_17 (ite AVERAGE_17 false true)))))) (let ((?v_151 (ite ?v_67 0 (ite ?v_133 ?v_134 ?v_152))) (?v_132 (ite ?v_67 0 (ite ?v_133 ?v_104 ?v_134))) (?v_169 (ite ?v_67 0 (ite ?v_133 ?v_152 ?v_170))) (?v_2 (ite (or ?v_66 ?v_65) 2 1)) (?v_268 (or ?v_66 (and ?v_65 (and (ite RESTART_17 false true) (ite (and ENABLE_17 AVERAGE_17) false true))))) (?v_102 (ite ?v_67 0 DATA_IN_17))) (let ((?v_265 (ite (and ?v_65 ENABLE_17) ?v_102 (ite ?v_67 0 ?v_269))) (?v_193 (ite (or ?v_66 (and ?v_65 (> ?v_192 DATA_IN_17))) DATA_IN_17 ?v_192)) (?v_176 (ite (or ?v_66 (and ?v_65 (> DATA_IN_17 ?v_175))) DATA_IN_17 ?v_175)) (?v_266 (ite ?v_131 ?v_169 (ite ?v_67 0 ?v_270))) (?v_62 (= ?v_2 2)) (?v_63 (= ?v_2 1))) (let ((?v_129 (and ?v_99 ?v_62)) (?v_64 (and ?v_99 ?v_63)) (?v_267 (and ?v_62 (or RESTART_16 (and ENABLE_16 (ite AVERAGE_16 false true))))) (?v_3 (ite (or ?v_63 ?v_62) 2 1))) (let ((?v_130 (ite ?v_64 0 (ite ?v_131 ?v_102 ?v_132))) (?v_264 (or ?v_63 (and ?v_62 (and (ite RESTART_16 false true) (ite (and ENABLE_16 AVERAGE_16) false true))))) (?v_168 (ite ?v_64 0 (ite ?v_131 ?v_151 ?v_169))) (?v_150 (ite ?v_64 0 (ite ?v_131 ?v_132 ?v_151))) (?v_194 (ite (or ?v_63 (and ?v_62 (> ?v_193 DATA_IN_16))) DATA_IN_16 ?v_193)) (?v_177 (ite (or ?v_63 (and ?v_62 (> DATA_IN_16 ?v_176))) DATA_IN_16 ?v_176)) (?v_100 (ite ?v_64 0 DATA_IN_16))) (let ((?v_261 (ite (and ?v_62 ENABLE_16) ?v_100 (ite ?v_64 0 ?v_265))) (?v_262 (ite ?v_129 ?v_168 (ite ?v_64 0 ?v_266))) (?v_59 (= ?v_3 2)) (?v_60 (= ?v_3 1))) (let ((?v_263 (and ?v_59 (or RESTART_15 (and ENABLE_15 (ite AVERAGE_15 false true))))) (?v_61 (and ?v_97 ?v_60)) (?v_127 (and ?v_97 ?v_59)) (?v_4 (ite (or ?v_60 ?v_59) 2 1))) (let ((?v_149 (ite ?v_61 0 (ite ?v_129 ?v_130 ?v_150))) (?v_128 (ite ?v_61 0 (ite ?v_129 ?v_100 ?v_130))) (?v_167 (ite ?v_61 0 (ite ?v_129 ?v_150 ?v_168))) (?v_260 (or ?v_60 (and ?v_59 (and (ite RESTART_15 false true) (ite (and ENABLE_15 AVERAGE_15) false true))))) (?v_178 (ite (or ?v_60 (and ?v_59 (> DATA_IN_15 ?v_177))) DATA_IN_15 ?v_177)) (?v_98 (ite ?v_61 0 DATA_IN_15))) (let ((?v_257 (ite (and ?v_59 ENABLE_15) ?v_98 (ite ?v_61 0 ?v_261))) (?v_258 (ite ?v_127 ?v_167 (ite ?v_61 0 ?v_262))) (?v_195 (ite (or ?v_60 (and ?v_59 (> ?v_194 DATA_IN_15))) DATA_IN_15 ?v_194)) (?v_57 (= ?v_4 1)) (?v_56 (= ?v_4 2))) (let ((?v_259 (and ?v_56 (or RESTART_14 (and ENABLE_14 (ite AVERAGE_14 false true))))) (?v_58 (and ?v_95 ?v_57)) (?v_125 (and ?v_95 ?v_56))) (let ((?v_126 (ite ?v_58 0 (ite ?v_127 ?v_98 ?v_128))) (?v_148 (ite ?v_58 0 (ite ?v_127 ?v_128 ?v_149))) (?v_166 (ite ?v_58 0 (ite ?v_127 ?v_149 ?v_167))) (?v_5 (ite (or ?v_57 ?v_56) 2 1)) (?v_256 (or ?v_57 (and ?v_56 (and (ite RESTART_14 false true) (ite (and ENABLE_14 AVERAGE_14) false true)))))) (let ((?v_254 (ite ?v_125 ?v_166 (ite ?v_58 0 ?v_258))) (?v_179 (ite (or ?v_57 (and ?v_56 (> DATA_IN_14 ?v_178))) DATA_IN_14 ?v_178)) (?v_196 (ite (or ?v_57 (and ?v_56 (> ?v_195 DATA_IN_14))) DATA_IN_14 ?v_195)) (?v_96 (ite ?v_58 0 DATA_IN_14))) (let ((?v_253 (ite (and ?v_56 ENABLE_14) ?v_96 (ite ?v_58 0 ?v_257))) (?v_53 (= ?v_5 2)) (?v_54 (= ?v_5 1))) (let ((?v_55 (and ?v_93 ?v_54)) (?v_255 (and ?v_53 (or RESTART_13 (and ENABLE_13 (ite AVERAGE_13 false true))))) (?v_123 (and ?v_93 ?v_53)) (?v_252 (or ?v_54 (and ?v_53 (and (ite RESTART_13 false true) (ite (and ENABLE_13 AVERAGE_13) false true)))))) (let ((?v_147 (ite ?v_55 0 (ite ?v_125 ?v_126 ?v_148))) (?v_124 (ite ?v_55 0 (ite ?v_125 ?v_96 ?v_126))) (?v_6 (ite (or ?v_54 ?v_53) 2 1)) (?v_165 (ite ?v_55 0 (ite ?v_125 ?v_148 ?v_166))) (?v_197 (ite (or ?v_54 (and ?v_53 (> ?v_196 DATA_IN_13))) DATA_IN_13 ?v_196)) (?v_180 (ite (or ?v_54 (and ?v_53 (> DATA_IN_13 ?v_179))) DATA_IN_13 ?v_179))) (let ((?v_250 (ite ?v_123 ?v_165 (ite ?v_55 0 ?v_254))) (?v_94 (ite ?v_55 0 DATA_IN_13))) (let ((?v_249 (ite (and ?v_53 ENABLE_13) ?v_94 (ite ?v_55 0 ?v_253))) (?v_50 (= ?v_6 2)) (?v_51 (= ?v_6 1))) (let ((?v_52 (and ?v_91 ?v_51)) (?v_121 (and ?v_91 ?v_50)) (?v_251 (and ?v_50 (or RESTART_12 (and ENABLE_12 (ite AVERAGE_12 false true)))))) (let ((?v_164 (ite ?v_52 0 (ite ?v_123 ?v_147 ?v_165))) (?v_248 (or ?v_51 (and ?v_50 (and (ite RESTART_12 false true) (ite (and ENABLE_12 AVERAGE_12) false true))))) (?v_122 (ite ?v_52 0 (ite ?v_123 ?v_94 ?v_124))) (?v_7 (ite (or ?v_51 ?v_50) 2 1)) (?v_146 (ite ?v_52 0 (ite ?v_123 ?v_124 ?v_147))) (?v_198 (ite (or ?v_51 (and ?v_50 (> ?v_197 DATA_IN_12))) DATA_IN_12 ?v_197)) (?v_181 (ite (or ?v_51 (and ?v_50 (> DATA_IN_12 ?v_180))) DATA_IN_12 ?v_180)) (?v_92 (ite ?v_52 0 DATA_IN_12))) (let ((?v_245 (ite (and ?v_50 ENABLE_12) ?v_92 (ite ?v_52 0 ?v_249))) (?v_246 (ite ?v_121 ?v_164 (ite ?v_52 0 ?v_250))) (?v_47 (= ?v_7 2)) (?v_48 (= ?v_7 1))) (let ((?v_49 (and ?v_89 ?v_48)) (?v_247 (and ?v_47 (or RESTART_11 (and ENABLE_11 (ite AVERAGE_11 false true))))) (?v_119 (and ?v_89 ?v_47)) (?v_244 (or ?v_48 (and ?v_47 (and (ite RESTART_11 false true) (ite (and ENABLE_11 AVERAGE_11) false true))))) (?v_8 (ite (or ?v_48 ?v_47) 2 1))) (let ((?v_163 (ite ?v_49 0 (ite ?v_121 ?v_146 ?v_164))) (?v_120 (ite ?v_49 0 (ite ?v_121 ?v_92 ?v_122))) (?v_145 (ite ?v_49 0 (ite ?v_121 ?v_122 ?v_146)))) (let ((?v_242 (ite ?v_119 ?v_163 (ite ?v_49 0 ?v_246))) (?v_199 (ite (or ?v_48 (and ?v_47 (> ?v_198 DATA_IN_11))) DATA_IN_11 ?v_198)) (?v_182 (ite (or ?v_48 (and ?v_47 (> DATA_IN_11 ?v_181))) DATA_IN_11 ?v_181)) (?v_90 (ite ?v_49 0 DATA_IN_11))) (let ((?v_241 (ite (and ?v_47 ENABLE_11) ?v_90 (ite ?v_49 0 ?v_245))) (?v_44 (= ?v_8 2)) (?v_45 (= ?v_8 1))) (let ((?v_243 (and ?v_44 (or RESTART_10 (and ENABLE_10 (ite AVERAGE_10 false true))))) (?v_46 (and ?v_87 ?v_45)) (?v_117 (and ?v_87 ?v_44)) (?v_240 (or ?v_45 (and ?v_44 (and (ite RESTART_10 false true) (ite (and ENABLE_10 AVERAGE_10) false true))))) (?v_9 (ite (or ?v_45 ?v_44) 2 1))) (let ((?v_118 (ite ?v_46 0 (ite ?v_119 ?v_90 ?v_120))) (?v_144 (ite ?v_46 0 (ite ?v_119 ?v_120 ?v_145))) (?v_162 (ite ?v_46 0 (ite ?v_119 ?v_145 ?v_163)))) (let ((?v_238 (ite ?v_117 ?v_162 (ite ?v_46 0 ?v_242))) (?v_88 (ite ?v_46 0 DATA_IN_10))) (let ((?v_237 (ite (and ?v_44 ENABLE_10) ?v_88 (ite ?v_46 0 ?v_241))) (?v_200 (ite (or ?v_45 (and ?v_44 (> ?v_199 DATA_IN_10))) DATA_IN_10 ?v_199)) (?v_183 (ite (or ?v_45 (and ?v_44 (> DATA_IN_10 ?v_182))) DATA_IN_10 ?v_182)) (?v_41 (= ?v_9 2)) (?v_42 (= ?v_9 1))) (let ((?v_43 (and ?v_85 ?v_42)) (?v_239 (and ?v_41 (or RESTART_9 (and ENABLE_9 (ite AVERAGE_9 false true))))) (?v_115 (and ?v_85 ?v_41))) (let ((?v_161 (ite ?v_43 0 (ite ?v_117 ?v_144 ?v_162))) (?v_143 (ite ?v_43 0 (ite ?v_117 ?v_118 ?v_144))) (?v_116 (ite ?v_43 0 (ite ?v_117 ?v_88 ?v_118))) (?v_10 (ite (or ?v_42 ?v_41) 2 1)) (?v_236 (or ?v_42 (and ?v_41 (and (ite RESTART_9 false true) (ite (and ENABLE_9 AVERAGE_9) false true))))) (?v_86 (ite ?v_43 0 DATA_IN_9))) (let ((?v_233 (ite (and ?v_41 ENABLE_9) ?v_86 (ite ?v_43 0 ?v_237))) (?v_234 (ite ?v_115 ?v_161 (ite ?v_43 0 ?v_238))) (?v_184 (ite (or ?v_42 (and ?v_41 (> DATA_IN_9 ?v_183))) DATA_IN_9 ?v_183)) (?v_201 (ite (or ?v_42 (and ?v_41 (> ?v_200 DATA_IN_9))) DATA_IN_9 ?v_200)) (?v_38 (= ?v_10 2)) (?v_39 (= ?v_10 1))) (let ((?v_113 (and ?v_83 ?v_38)) (?v_235 (and ?v_38 (or RESTART_8 (and ENABLE_8 (ite AVERAGE_8 false true))))) (?v_40 (and ?v_83 ?v_39)) (?v_232 (or ?v_39 (and ?v_38 (and (ite RESTART_8 false true) (ite (and ENABLE_8 AVERAGE_8) false true)))))) (let ((?v_160 (ite ?v_40 0 (ite ?v_115 ?v_143 ?v_161))) (?v_142 (ite ?v_40 0 (ite ?v_115 ?v_116 ?v_143))) (?v_114 (ite ?v_40 0 (ite ?v_115 ?v_86 ?v_116))) (?v_11 (ite (or ?v_39 ?v_38) 2 1)) (?v_185 (ite (or ?v_39 (and ?v_38 (> DATA_IN_8 ?v_184))) DATA_IN_8 ?v_184))) (let ((?v_230 (ite ?v_113 ?v_160 (ite ?v_40 0 ?v_234))) (?v_84 (ite ?v_40 0 DATA_IN_8))) (let ((?v_229 (ite (and ?v_38 ENABLE_8) ?v_84 (ite ?v_40 0 ?v_233))) (?v_202 (ite (or ?v_39 (and ?v_38 (> ?v_201 DATA_IN_8))) DATA_IN_8 ?v_201)) (?v_35 (= ?v_11 2)) (?v_36 (= ?v_11 1))) (let ((?v_111 (and ?v_81 ?v_35)) (?v_231 (and ?v_35 (or RESTART_7 (and ENABLE_7 (ite AVERAGE_7 false true))))) (?v_37 (and ?v_81 ?v_36)) (?v_228 (or ?v_36 (and ?v_35 (and (ite RESTART_7 false true) (ite (and ENABLE_7 AVERAGE_7) false true))))) (?v_12 (ite (or ?v_36 ?v_35) 2 1))) (let ((?v_141 (ite ?v_37 0 (ite ?v_113 ?v_114 ?v_142))) (?v_159 (ite ?v_37 0 (ite ?v_113 ?v_142 ?v_160))) (?v_112 (ite ?v_37 0 (ite ?v_113 ?v_84 ?v_114))) (?v_203 (ite (or ?v_36 (and ?v_35 (> ?v_202 DATA_IN_7))) DATA_IN_7 ?v_202))) (let ((?v_226 (ite ?v_111 ?v_159 (ite ?v_37 0 ?v_230))) (?v_82 (ite ?v_37 0 DATA_IN_7))) (let ((?v_225 (ite (and ?v_35 ENABLE_7) ?v_82 (ite ?v_37 0 ?v_229))) (?v_186 (ite (or ?v_36 (and ?v_35 (> DATA_IN_7 ?v_185))) DATA_IN_7 ?v_185)) (?v_32 (= ?v_12 2)) (?v_33 (= ?v_12 1))) (let ((?v_34 (and ?v_79 ?v_33)) (?v_109 (and ?v_79 ?v_32)) (?v_227 (and ?v_32 (or RESTART_6 (and ENABLE_6 (ite AVERAGE_6 false true))))) (?v_13 (ite (or ?v_33 ?v_32) 2 1)) (?v_224 (or ?v_33 (and ?v_32 (and (ite RESTART_6 false true) (ite (and ENABLE_6 AVERAGE_6) false true)))))) (let ((?v_110 (ite ?v_34 0 (ite ?v_111 ?v_82 ?v_112))) (?v_140 (ite ?v_34 0 (ite ?v_111 ?v_112 ?v_141))) (?v_158 (ite ?v_34 0 (ite ?v_111 ?v_141 ?v_159))) (?v_187 (ite (or ?v_33 (and ?v_32 (> DATA_IN_6 ?v_186))) DATA_IN_6 ?v_186)) (?v_204 (ite (or ?v_33 (and ?v_32 (> ?v_203 DATA_IN_6))) DATA_IN_6 ?v_203))) (let ((?v_222 (ite ?v_109 ?v_158 (ite ?v_34 0 ?v_226))) (?v_80 (ite ?v_34 0 DATA_IN_6))) (let ((?v_221 (ite (and ?v_32 ENABLE_6) ?v_80 (ite ?v_34 0 ?v_225))) (?v_29 (= ?v_13 2)) (?v_30 (= ?v_13 1))) (let ((?v_223 (and ?v_29 (or RESTART_5 (and ENABLE_5 (ite AVERAGE_5 false true))))) (?v_107 (and ?v_77 ?v_29)) (?v_31 (and ?v_77 ?v_30)) (?v_14 (ite (or ?v_30 ?v_29) 2 1)) (?v_220 (or ?v_30 (and ?v_29 (and (ite RESTART_5 false true) (ite (and ENABLE_5 AVERAGE_5) false true)))))) (let ((?v_108 (ite ?v_31 0 (ite ?v_109 ?v_80 ?v_110))) (?v_139 (ite ?v_31 0 (ite ?v_109 ?v_110 ?v_140))) (?v_157 (ite ?v_31 0 (ite ?v_109 ?v_140 ?v_158))) (?v_188 (ite (or ?v_30 (and ?v_29 (> DATA_IN_5 ?v_187))) DATA_IN_5 ?v_187)) (?v_205 (ite (or ?v_30 (and ?v_29 (> ?v_204 DATA_IN_5))) DATA_IN_5 ?v_204)) (?v_78 (ite ?v_31 0 DATA_IN_5))) (let ((?v_217 (ite (and ?v_29 ENABLE_5) ?v_78 (ite ?v_31 0 ?v_221))) (?v_218 (ite ?v_107 ?v_157 (ite ?v_31 0 ?v_222))) (?v_26 (= ?v_14 2)) (?v_27 (= ?v_14 1))) (let ((?v_137 (and ?v_76 ?v_26)) (?v_28 (and ?v_76 ?v_27)) (?v_219 (and ?v_26 (or RESTART_4 (and ENABLE_4 (ite AVERAGE_4 false true))))) (?v_216 (or ?v_27 (and ?v_26 (and (ite RESTART_4 false true) (ite (and ENABLE_4 AVERAGE_4) false true))))) (?v_15 (ite (or ?v_27 ?v_26) 2 1))) (let ((?v_156 (ite ?v_28 0 (ite ?v_107 ?v_139 ?v_157))) (?v_138 (ite ?v_28 0 (ite ?v_107 ?v_108 ?v_139)))) (let ((?v_214 (ite ?v_137 ?v_156 (ite ?v_28 0 ?v_218))) (?v_213 (ite (and ?v_26 ENABLE_4) (ite ?v_28 0 DATA_IN_4) (ite ?v_28 0 ?v_217))) (?v_206 (ite (or ?v_27 (and ?v_26 (> ?v_205 DATA_IN_4))) DATA_IN_4 ?v_205)) (?v_189 (ite (or ?v_27 (and ?v_26 (> DATA_IN_4 ?v_188))) DATA_IN_4 ?v_188)) (?v_23 (= ?v_15 2)) (?v_24 (= ?v_15 1))) (let ((?v_154 (and ?v_75 ?v_23)) (?v_25 (and ?v_75 ?v_24)) (?v_215 (and ?v_23 (or RESTART_3 (and ENABLE_3 (ite AVERAGE_3 false true)))))) (let ((?v_155 (ite ?v_25 0 (ite ?v_137 ?v_138 ?v_156))) (?v_212 (or ?v_24 (and ?v_23 (and (ite RESTART_3 false true) (ite (and ENABLE_3 AVERAGE_3) false true))))) (?v_16 (ite (or ?v_24 ?v_23) 2 1))) (let ((?v_210 (ite ?v_154 ?v_155 (ite ?v_25 0 ?v_214))) (?v_209 (ite (and ?v_23 ENABLE_3) (ite ?v_25 0 DATA_IN_3) (ite ?v_25 0 ?v_213))) (?v_207 (ite (or ?v_24 (and ?v_23 (> ?v_206 DATA_IN_3))) DATA_IN_3 ?v_206)) (?v_190 (ite (or ?v_24 (and ?v_23 (> DATA_IN_3 ?v_189))) DATA_IN_3 ?v_189)) (?v_21 (= ?v_16 1)) (?v_20 (= ?v_16 2))) (let ((?v_211 (and ?v_20 (or RESTART_2 (and ENABLE_2 (ite AVERAGE_2 false true))))) (?v_22 (and ?v_74 ?v_21)) (?v_208 (or ?v_21 (and ?v_20 (and (ite RESTART_2 false true) (ite (and ENABLE_2 AVERAGE_2) false true))))) (?v_17 (ite (or ?v_21 ?v_20) 2 1))) (let ((?v_173 (ite (and ?v_74 ?v_20) (ite ?v_22 0 (ite ?v_154 (ite ?v_25 0 (ite ?v_137 (ite ?v_28 0 (ite ?v_107 ?v_78 ?v_108)) ?v_138)) ?v_155)) (ite ?v_22 0 ?v_210))) (?v_18 (= ?v_17 2))) (let ((?v_172 (and ?v_18 (or RESTART_1 (and ENABLE_1 (ite AVERAGE_1 false true))))) (?v_19 (or (= ?v_17 1) (and ?v_18 (and (ite RESTART_1 false true) (ite (and ENABLE_1 AVERAGE_1) false true)))))) (not (= (and (and (and (and (and (and (and (and (and (ite (= (ite ?v_19 (ite ?v_172 0 (ite ?v_19 (ite (and ?v_20 ENABLE_2) (ite ?v_22 0 DATA_IN_2) (ite ?v_22 0 ?v_209)) ?v_173)) (ite ?v_172 (ite ?v_19 (+ DATA_IN_1 ?v_173) (+ (ite (or ?v_21 (and ?v_20 (> DATA_IN_2 ?v_190))) DATA_IN_2 ?v_190) (ite (or ?v_21 (and ?v_20 (> ?v_207 DATA_IN_2))) DATA_IN_2 ?v_207))) (ite ?v_19 0 (ite ?v_208 (ite ?v_211 0 (ite ?v_208 ?v_209 ?v_210)) (ite ?v_211 (ite ?v_208 (+ DATA_IN_2 ?v_210) (+ ?v_190 ?v_207)) (ite ?v_208 0 (ite ?v_212 (ite ?v_215 0 (ite ?v_212 ?v_213 ?v_214)) (ite ?v_215 (ite ?v_212 (+ DATA_IN_3 ?v_214) (+ ?v_189 ?v_206)) (ite ?v_212 0 (ite ?v_216 (ite ?v_219 0 (ite ?v_216 ?v_217 ?v_218)) (ite ?v_219 (ite ?v_216 (+ DATA_IN_4 ?v_218) (+ ?v_188 ?v_205)) (ite ?v_216 0 (ite ?v_220 (ite ?v_223 0 (ite ?v_220 ?v_221 ?v_222)) (ite ?v_223 (ite ?v_220 (+ DATA_IN_5 ?v_222) (+ ?v_187 ?v_204)) (ite ?v_220 0 (ite ?v_224 (ite ?v_227 0 (ite ?v_224 ?v_225 ?v_226)) (ite ?v_227 (ite ?v_224 (+ DATA_IN_6 ?v_226) (+ ?v_186 ?v_203)) (ite ?v_224 0 (ite ?v_228 (ite ?v_231 0 (ite ?v_228 ?v_229 ?v_230)) (ite ?v_231 (ite ?v_228 (+ DATA_IN_7 ?v_230) (+ ?v_185 ?v_202)) (ite ?v_228 0 (ite ?v_232 (ite ?v_235 0 (ite ?v_232 ?v_233 ?v_234)) (ite ?v_235 (ite ?v_232 (+ DATA_IN_8 ?v_234) (+ ?v_184 ?v_201)) (ite ?v_232 0 (ite ?v_236 (ite ?v_239 0 (ite ?v_236 ?v_237 ?v_238)) (ite ?v_239 (ite ?v_236 (+ DATA_IN_9 ?v_238) (+ ?v_183 ?v_200)) (ite ?v_236 0 (ite ?v_240 (ite ?v_243 0 (ite ?v_240 ?v_241 ?v_242)) (ite ?v_243 (ite ?v_240 (+ DATA_IN_10 ?v_242) (+ ?v_182 ?v_199)) (ite ?v_240 0 (ite ?v_244 (ite ?v_247 0 (ite ?v_244 ?v_245 ?v_246)) (ite ?v_247 (ite ?v_244 (+ DATA_IN_11 ?v_246) (+ ?v_181 ?v_198)) (ite ?v_244 0 (ite ?v_248 (ite ?v_251 0 (ite ?v_248 ?v_249 ?v_250)) (ite ?v_251 (ite ?v_248 (+ DATA_IN_12 ?v_250) (+ ?v_180 ?v_197)) (ite ?v_248 0 (ite ?v_252 (ite ?v_255 0 (ite ?v_252 ?v_253 ?v_254)) (ite ?v_255 (ite ?v_252 (+ DATA_IN_13 ?v_254) (+ ?v_179 ?v_196)) (ite ?v_252 0 (ite ?v_256 (ite ?v_259 0 (ite ?v_256 ?v_257 ?v_258)) (ite ?v_259 (ite ?v_256 (+ DATA_IN_14 ?v_258) (+ ?v_178 ?v_195)) (ite ?v_256 0 (ite ?v_260 (ite ?v_263 0 (ite ?v_260 ?v_261 ?v_262)) (ite ?v_263 (ite ?v_260 (+ DATA_IN_15 ?v_262) (+ ?v_177 ?v_194)) (ite ?v_260 0 (ite ?v_264 (ite ?v_267 0 (ite ?v_264 ?v_265 ?v_266)) (ite ?v_267 (ite ?v_264 (+ DATA_IN_16 ?v_266) (+ ?v_176 ?v_193)) (ite ?v_264 0 (ite ?v_268 (ite ?v_271 0 (ite ?v_268 ?v_269 ?v_270)) (ite ?v_271 (ite ?v_268 (+ DATA_IN_17 ?v_270) (+ ?v_175 ?v_192)) (ite ?v_268 0 (ite ?v_272 (ite ?v_275 0 (ite ?v_272 ?v_273 ?v_274)) (ite ?v_275 (ite ?v_272 (+ DATA_IN_18 ?v_274) (+ ?v_174 ?v_191)) (ite ?v_272 0 (ite ?v_276 (ite ?v_277 0 (ite ?v_276 Rlast_Reg_19 Reg4_Reg_19)) (ite ?v_277 (ite ?v_276 (+ DATA_IN_19 Reg4_Reg_19) (+ Rmax_Reg_19 Rmin_Reg_19)) (ite ?v_276 0 DATA_OUT_19))))))))))))))))))))))))))))))))))))))))))))))))))))))))) 1) true false) (= stato_reg_19 0)) (= Reg1_Reg_19 0)) (= Reg2_Reg_19 0)) (= Reg3_Reg_19 0)) (= Reg4_Reg_19 0)) (= Rmax_Reg_19 0)) (= Rmin_Reg_19 0)) (= Rlast_Reg_19 0)) (= DATA_OUT_19 0)) false)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
(exit)
