(set-logic QF_ALIA)
(set-info :source |
Unbounded version of the queue lock algorithm.


|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x_0 () Int)
(declare-fun x_1 () Int)
(declare-fun x_2 () (Array Int Int))
(declare-fun x_3 () Int)
(declare-fun x_4 () Int)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Int)
(declare-fun x_7 () (Array Int Int))
(declare-fun x_8 () Int)
(declare-fun x_9 () (Array Int Int))
(declare-fun x_10 () Int)
(declare-fun x_11 () Bool)
(declare-fun x_12 () Int)
(declare-fun x_13 () Int)
(declare-fun x_14 () Int)
(declare-fun x_15 () Int)
(declare-fun x_16 () Int)
(declare-fun x_17 () (Array Int Int))
(declare-fun x_18 () Int)
(declare-fun x_19 () Int)
(declare-fun x_20 () Int)
(declare-fun x_21 () Int)
(declare-fun x_22 () Int)
(declare-fun x_23 () (Array Int Int))
(declare-fun x_24 () Int)
(declare-fun x_25 () Bool)
(declare-fun x_26 () Int)
(declare-fun x_27 () Int)
(declare-fun x_28 () Int)
(declare-fun x_29 () Int)
(declare-fun x_30 () Int)
(declare-fun x_31 () (Array Int Int))
(declare-fun x_32 () Int)
(declare-fun x_33 () Int)
(declare-fun x_34 () Int)
(declare-fun x_35 () Int)
(declare-fun x_36 () Int)
(declare-fun x_37 () (Array Int Int))
(declare-fun x_38 () Int)
(declare-fun x_39 () Bool)
(declare-fun x_40 () Int)
(declare-fun x_41 () Int)
(declare-fun x_42 () Int)
(declare-fun x_43 () Int)
(declare-fun x_44 () Int)
(declare-fun x_45 () (Array Int Int))
(declare-fun x_46 () Int)
(declare-fun x_47 () Int)
(declare-fun x_48 () Int)
(declare-fun x_49 () Int)
(declare-fun x_50 () Int)
(declare-fun x_51 () (Array Int Int))
(declare-fun x_52 () Int)
(declare-fun x_53 () Bool)
(declare-fun x_54 () Int)
(declare-fun x_55 () Int)
(declare-fun x_56 () Int)
(declare-fun x_57 () Int)
(declare-fun x_58 () Int)
(declare-fun x_59 () (Array Int Int))
(declare-fun x_60 () Int)
(declare-fun x_61 () Int)
(declare-fun x_62 () Int)
(declare-fun x_63 () Int)
(declare-fun x_64 () Int)
(declare-fun x_65 () (Array Int Int))
(declare-fun x_66 () Int)
(declare-fun x_67 () Bool)
(declare-fun x_68 () Int)
(declare-fun x_69 () Int)
(declare-fun x_70 () Int)
(declare-fun x_71 () Int)
(declare-fun x_72 () Int)
(declare-fun x_73 () (Array Int Int))
(declare-fun x_74 () Int)
(declare-fun x_75 () Int)
(declare-fun x_76 () Int)
(declare-fun x_77 () Int)
(declare-fun x_78 () Int)
(declare-fun x_79 () (Array Int Int))
(declare-fun x_80 () Int)
(declare-fun x_81 () Bool)
(declare-fun x_82 () Int)
(declare-fun x_83 () Int)
(declare-fun x_84 () Int)
(declare-fun x_85 () Int)
(declare-fun x_86 () Int)
(declare-fun x_87 () (Array Int Int))
(declare-fun x_88 () Int)
(declare-fun x_89 () Int)
(declare-fun x_90 () Int)
(declare-fun x_91 () Int)
(declare-fun x_92 () Int)
(declare-fun x_93 () (Array Int Int))
(declare-fun x_94 () Int)
(declare-fun x_95 () Bool)
(declare-fun x_96 () Int)
(declare-fun x_97 () Int)
(declare-fun x_98 () Int)
(declare-fun x_99 () Int)
(declare-fun x_100 () Int)
(declare-fun x_101 () (Array Int Int))
(declare-fun x_102 () Int)
(declare-fun x_103 () Int)
(declare-fun x_104 () Int)
(declare-fun x_105 () Int)
(declare-fun x_106 () Int)
(declare-fun x_107 () (Array Int Int))
(declare-fun x_108 () Int)
(declare-fun x_109 () Bool)
(declare-fun x_110 () Int)
(declare-fun x_111 () Int)
(declare-fun x_112 () Int)
(declare-fun x_113 () Int)
(declare-fun x_114 () Int)
(declare-fun x_115 () (Array Int Int))
(declare-fun x_116 () Int)
(declare-fun x_117 () Int)
(declare-fun x_118 () Int)
(declare-fun x_119 () Int)
(declare-fun x_120 () Int)
(declare-fun x_121 () (Array Int Int))
(declare-fun x_122 () Int)
(declare-fun x_123 () Bool)
(declare-fun x_124 () Int)
(declare-fun x_125 () Int)
(declare-fun x_126 () Int)
(declare-fun x_127 () Int)
(declare-fun x_128 () Int)
(declare-fun x_129 () (Array Int Int))
(declare-fun x_130 () Int)
(declare-fun x_131 () Int)
(declare-fun x_132 () Int)
(declare-fun x_133 () Int)
(declare-fun x_134 () Int)
(declare-fun x_135 () (Array Int Int))
(declare-fun x_136 () Int)
(declare-fun x_137 () Bool)
(declare-fun x_138 () Int)
(declare-fun x_139 () Int)
(declare-fun x_140 () Int)
(declare-fun x_141 () Int)
(declare-fun x_142 () Int)
(declare-fun x_143 () (Array Int Int))
(declare-fun x_144 () Int)
(declare-fun x_145 () Int)
(declare-fun x_146 () Int)
(declare-fun x_147 () Int)
(declare-fun x_148 () Int)
(declare-fun x_149 () (Array Int Int))
(declare-fun x_150 () Int)
(declare-fun x_151 () Bool)
(declare-fun x_152 () Int)
(declare-fun x_153 () Int)
(declare-fun x_154 () Int)
(declare-fun x_155 () Int)
(declare-fun x_156 () Int)
(declare-fun x_157 () (Array Int Int))
(declare-fun x_158 () Int)
(declare-fun x_159 () Int)
(declare-fun x_160 () Int)
(declare-fun x_161 () Int)
(declare-fun x_162 () Int)
(declare-fun x_163 () (Array Int Int))
(declare-fun x_164 () Int)
(declare-fun x_165 () Bool)
(declare-fun x_166 () Int)
(declare-fun x_167 () Int)
(declare-fun x_168 () Int)
(declare-fun x_169 () Int)
(declare-fun x_170 () Int)
(declare-fun x_171 () (Array Int Int))
(declare-fun x_172 () Int)
(declare-fun x_173 () Int)
(declare-fun x_174 () Int)
(declare-fun x_175 () Int)
(declare-fun x_176 () Int)
(declare-fun x_177 () (Array Int Int))
(declare-fun x_178 () Int)
(declare-fun x_179 () Bool)
(declare-fun x_180 () Int)
(declare-fun x_181 () Int)
(declare-fun x_182 () Int)
(declare-fun x_183 () Int)
(declare-fun x_184 () Int)
(declare-fun x_185 () (Array Int Int))
(declare-fun x_186 () Int)
(declare-fun x_187 () Int)
(declare-fun x_188 () Int)
(declare-fun x_189 () Int)
(declare-fun x_190 () Int)
(declare-fun x_191 () (Array Int Int))
(declare-fun x_192 () Int)
(declare-fun x_193 () Bool)
(declare-fun x_194 () Int)
(declare-fun x_195 () Int)
(declare-fun x_196 () Int)
(declare-fun x_197 () Int)
(declare-fun x_198 () Int)
(declare-fun x_199 () (Array Int Int))
(declare-fun x_200 () Int)
(declare-fun x_201 () Int)
(declare-fun x_202 () Int)
(declare-fun x_203 () Int)
(declare-fun x_204 () Int)
(declare-fun x_205 () (Array Int Int))
(declare-fun x_206 () Int)
(declare-fun x_207 () Bool)
(declare-fun x_208 () Int)
(declare-fun x_209 () Int)
(declare-fun x_210 () Int)
(declare-fun x_211 () Int)
(declare-fun x_212 () Int)
(declare-fun x_213 () (Array Int Int))
(declare-fun x_214 () Int)
(declare-fun x_215 () Int)
(declare-fun x_216 () Int)
(declare-fun x_217 () Int)
(declare-fun x_218 () Int)
(declare-fun x_219 () (Array Int Int))
(declare-fun x_220 () Int)
(declare-fun x_221 () Bool)
(declare-fun x_222 () Int)
(declare-fun x_223 () Int)
(declare-fun x_224 () Int)
(declare-fun x_225 () Int)
(declare-fun x_226 () Int)
(declare-fun x_227 () (Array Int Int))
(declare-fun x_228 () Int)
(declare-fun x_229 () Int)
(declare-fun x_230 () Int)
(declare-fun x_231 () Int)
(declare-fun x_232 () Int)
(declare-fun x_233 () (Array Int Int))
(declare-fun x_234 () Int)
(declare-fun x_235 () Bool)
(declare-fun x_236 () Int)
(declare-fun x_237 () Int)
(declare-fun x_238 () Int)
(declare-fun x_239 () Int)
(declare-fun x_240 () Int)
(declare-fun x_241 () (Array Int Int))
(declare-fun x_242 () Int)
(declare-fun x_243 () Int)
(declare-fun x_244 () Int)
(declare-fun x_245 () Int)
(declare-fun x_246 () Int)
(declare-fun x_247 () (Array Int Int))
(declare-fun x_248 () Int)
(declare-fun x_249 () Bool)
(declare-fun x_250 () Int)
(declare-fun x_251 () Int)
(declare-fun x_252 () Int)
(declare-fun x_253 () Int)
(declare-fun x_254 () Int)
(declare-fun x_255 () (Array Int Int))
(declare-fun x_256 () Int)
(declare-fun x_257 () Int)
(declare-fun x_258 () Int)
(declare-fun x_259 () Int)
(declare-fun x_260 () Int)
(declare-fun x_261 () (Array Int Int))
(declare-fun x_262 () Int)
(declare-fun x_263 () Bool)
(declare-fun x_264 () Int)
(declare-fun x_265 () Int)
(declare-fun x_266 () Int)
(declare-fun x_267 () Int)
(declare-fun x_268 () Int)
(declare-fun x_269 () (Array Int Int))
(declare-fun x_270 () Int)
(declare-fun x_271 () Int)
(declare-fun x_272 () Int)
(declare-fun x_273 () Int)
(declare-fun x_274 () Int)
(declare-fun x_275 () Int)
(declare-fun x_276 () Int)
(declare-fun x_277 () Int)
(declare-fun x_278 () Int)
(declare-fun x_279 () Int)
(declare-fun x_280 () Int)
(declare-fun x_281 () Int)
(declare-fun x_282 () Int)
(declare-fun x_283 () Int)
(declare-fun x_284 () Int)
(declare-fun x_285 () Int)
(declare-fun x_286 () Int)
(declare-fun x_287 () Int)
(declare-fun x_288 () Int)
(declare-fun x_289 () Int)
(declare-fun x_290 () Int)
(declare-fun x_291 () Int)
(declare-fun x_292 () Int)
(declare-fun x_293 () Int)
(declare-fun x_294 () Int)
(declare-fun x_295 () Int)
(declare-fun x_296 () Int)
(declare-fun x_297 () Int)
(declare-fun x_298 () Int)
(declare-fun x_299 () Int)
(declare-fun x_300 () Int)
(declare-fun x_301 () Int)
(declare-fun x_302 () Int)
(declare-fun x_303 () Int)
(declare-fun x_304 () Int)
(declare-fun x_305 () Int)
(declare-fun x_306 () Int)
(declare-fun x_307 () Int)
(declare-fun x_308 () Int)
(declare-fun x_309 () Int)
(declare-fun x_310 () Int)
(declare-fun x_311 () Int)
(declare-fun x_312 () Int)
(declare-fun x_313 () Int)
(declare-fun x_314 () Int)
(declare-fun x_315 () Int)
(declare-fun x_316 () Int)
(declare-fun x_317 () Int)
(declare-fun x_318 () Int)
(declare-fun x_319 () Int)
(declare-fun x_320 () Int)
(declare-fun x_321 () Int)
(declare-fun x_322 () Int)
(declare-fun x_323 () Int)
(declare-fun x_324 () Int)
(declare-fun x_325 () Int)
(declare-fun x_326 () Int)
(declare-fun x_327 () Int)
(declare-fun x_328 () Int)
(declare-fun x_329 () Int)
(declare-fun x_330 () Int)
(declare-fun x_331 () Int)
(declare-fun x_332 () Int)
(declare-fun x_333 () Int)
(declare-fun x_334 () Int)
(declare-fun x_335 () Int)
(declare-fun x_336 () Int)
(declare-fun x_337 () Int)
(declare-fun x_338 () Int)
(declare-fun x_339 () Int)
(declare-fun x_340 () Int)
(declare-fun x_341 () Int)
(declare-fun x_342 () Int)
(declare-fun x_343 () Int)
(declare-fun x_344 () Int)
(declare-fun x_345 () Int)
(declare-fun x_346 () Int)
(declare-fun x_347 () Int)
(declare-fun x_348 () Int)
(declare-fun x_349 () Int)
(declare-fun x_350 () Int)
(declare-fun x_351 () Int)
(declare-fun x_352 () Int)
(declare-fun x_353 () Int)
(declare-fun x_354 () Int)
(declare-fun x_355 () Int)
(declare-fun x_356 () Int)
(declare-fun x_357 () Int)
(declare-fun x_358 () Int)
(declare-fun x_359 () Int)
(declare-fun x_360 () Int)
(declare-fun x_361 () Int)
(declare-fun x_362 () Int)
(declare-fun x_363 () Int)
(declare-fun x_364 () Int)
(declare-fun x_365 () Int)
(declare-fun x_366 () Int)
(declare-fun x_367 () Int)
(declare-fun x_368 () Int)
(declare-fun x_369 () Int)
(declare-fun x_370 () Int)
(declare-fun x_371 () Int)
(declare-fun x_372 () Int)
(declare-fun x_373 () Int)
(declare-fun x_374 () Int)
(declare-fun x_375 () Int)
(declare-fun x_376 () Int)
(declare-fun x_377 () Int)
(declare-fun x_378 () Int)
(declare-fun x_379 () Int)
(declare-fun x_380 () Int)
(declare-fun x_381 () Int)
(declare-fun x_382 () Int)
(declare-fun x_383 () Int)
(declare-fun x_384 () Int)
(declare-fun x_385 () Int)
(declare-fun x_386 () Int)
(declare-fun x_387 () Int)
(declare-fun x_388 () Int)
(declare-fun x_389 () Int)
(declare-fun x_390 () Int)
(declare-fun x_391 () Int)
(assert (let ((?v_93 (= x_9 x_7)) (?v_90 (= x_10 x_0)) (?v_91 (= x_11 x_5)) (?v_94 (= x_12 x_1)) (?v_92 (not (<= x_1 x_0))) (?v_88 (= x_23 x_9)) (?v_85 (= x_24 x_10)) (?v_86 (= x_25 x_11)) (?v_89 (= x_26 x_12)) (?v_87 (not (<= x_12 x_10))) (?v_83 (= x_37 x_23)) (?v_80 (= x_38 x_24)) (?v_81 (= x_39 x_25)) (?v_84 (= x_40 x_26)) (?v_82 (not (<= x_26 x_24))) (?v_78 (= x_51 x_37)) (?v_75 (= x_52 x_38)) (?v_76 (= x_53 x_39)) (?v_79 (= x_54 x_40)) (?v_77 (not (<= x_40 x_38))) (?v_73 (= x_65 x_51)) (?v_70 (= x_66 x_52)) (?v_71 (= x_67 x_53)) (?v_74 (= x_68 x_54)) (?v_72 (not (<= x_54 x_52))) (?v_68 (= x_79 x_65)) (?v_65 (= x_80 x_66)) (?v_66 (= x_81 x_67)) (?v_69 (= x_82 x_68)) (?v_67 (not (<= x_68 x_66))) (?v_63 (= x_93 x_79)) (?v_60 (= x_94 x_80)) (?v_61 (= x_95 x_81)) (?v_64 (= x_96 x_82)) (?v_62 (not (<= x_82 x_80))) (?v_58 (= x_107 x_93)) (?v_55 (= x_108 x_94)) (?v_56 (= x_109 x_95)) (?v_59 (= x_110 x_96)) (?v_57 (not (<= x_96 x_94))) (?v_53 (= x_121 x_107)) (?v_50 (= x_122 x_108)) (?v_51 (= x_123 x_109)) (?v_54 (= x_124 x_110)) (?v_52 (not (<= x_110 x_108))) (?v_48 (= x_135 x_121)) (?v_45 (= x_136 x_122)) (?v_46 (= x_137 x_123)) (?v_49 (= x_138 x_124)) (?v_47 (not (<= x_124 x_122))) (?v_43 (= x_149 x_135)) (?v_40 (= x_150 x_136)) (?v_41 (= x_151 x_137)) (?v_44 (= x_152 x_138)) (?v_42 (not (<= x_138 x_136))) (?v_38 (= x_163 x_149)) (?v_35 (= x_164 x_150)) (?v_36 (= x_165 x_151)) (?v_39 (= x_166 x_152)) (?v_37 (not (<= x_152 x_150))) (?v_33 (= x_177 x_163)) (?v_30 (= x_178 x_164)) (?v_31 (= x_179 x_165)) (?v_34 (= x_180 x_166)) (?v_32 (not (<= x_166 x_164))) (?v_28 (= x_191 x_177)) (?v_25 (= x_192 x_178)) (?v_26 (= x_193 x_179)) (?v_29 (= x_194 x_180)) (?v_27 (not (<= x_180 x_178))) (?v_23 (= x_205 x_191)) (?v_20 (= x_206 x_192)) (?v_21 (= x_207 x_193)) (?v_24 (= x_208 x_194)) (?v_22 (not (<= x_194 x_192))) (?v_18 (= x_219 x_205)) (?v_15 (= x_220 x_206)) (?v_16 (= x_221 x_207)) (?v_19 (= x_222 x_208)) (?v_17 (not (<= x_208 x_206))) (?v_13 (= x_233 x_219)) (?v_10 (= x_234 x_220)) (?v_11 (= x_235 x_221)) (?v_14 (= x_236 x_222)) (?v_12 (not (<= x_222 x_220))) (?v_8 (= x_247 x_233)) (?v_5 (= x_248 x_234)) (?v_6 (= x_249 x_235)) (?v_9 (= x_250 x_236)) (?v_7 (not (<= x_236 x_234))) (?v_3 (= x_261 x_247)) (?v_0 (= x_262 x_248)) (?v_1 (= x_263 x_249)) (?v_4 (= x_264 x_250)) (?v_2 (not (<= x_250 x_248))) (?v_95 (select x_2 x_3)) (?v_96 (select x_2 x_4))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (= x_4 x_3)) (= x_0 0)) (= x_1 0)) (= x_274 ?v_95)) (= x_274 1)) (= x_275 ?v_96)) (= x_275 1)) x_5) (= x_6 0)) (= x_276 (select x_7 x_0))) (= x_8 x_276)) (= x_277 (select x_9 x_10))) (= x_22 x_277)) (= x_278 (select x_23 x_24))) (= x_36 x_278)) (= x_279 (select x_37 x_38))) (= x_50 x_279)) (= x_280 (select x_51 x_52))) (= x_64 x_280)) (= x_281 (select x_65 x_66))) (= x_78 x_281)) (= x_282 (select x_79 x_80))) (= x_92 x_282)) (= x_283 (select x_93 x_94))) (= x_106 x_283)) (= x_284 (select x_107 x_108))) (= x_120 x_284)) (= x_285 (select x_121 x_122))) (= x_134 x_285)) (= x_286 (select x_135 x_136))) (= x_148 x_286)) (= x_287 (select x_149 x_150))) (= x_162 x_287)) (= x_288 (select x_163 x_164))) (= x_176 x_288)) (= x_289 (select x_177 x_178))) (= x_190 x_289)) (= x_290 (select x_191 x_192))) (= x_204 x_290)) (= x_291 (select x_205 x_206))) (= x_218 x_291)) (= x_292 (select x_219 x_220))) (= x_232 x_292)) (= x_293 (select x_233 x_234))) (= x_246 x_293)) (= x_294 (select x_247 x_248))) (= x_260 x_294)) (= x_265 (+ x_251 1))) (= x_295 (select x_255 x_267))) (= x_296 (select x_255 x_270))) (= x_297 (select x_255 x_272))) (or (or (or (and (and (and (and (and (and (and (= x_266 0) (= x_264 (+ x_250 1))) ?v_0) ?v_1) (= x_268 x_267)) (= x_295 1)) (= x_269 (store x_255 x_267 2))) (= x_261 (store x_247 x_250 x_267))) (and (and (and (and (and (and (and (and (and (= x_266 1) ?v_2) ?v_0) ?v_1) ?v_3) ?v_4) (= x_271 x_270)) (= x_296 2)) (= x_260 x_270)) (= x_269 (store x_255 x_270 3)))) (and (and (and (and (and (and (and (and (and (= x_266 2) ?v_2) (= x_262 (+ x_248 1))) ?v_1) ?v_3) ?v_4) (= x_273 x_272)) (= x_297 3)) (or (not (<= x_251 12)) (= x_260 x_272))) (= x_269 (store x_255 x_272 1)))) (and (and (and (and (and (= x_266 3) ?v_3) ?v_0) ?v_1) (= x_269 x_255)) ?v_4))) (= x_251 (+ x_237 1))) (= x_298 (select x_241 x_253))) (= x_299 (select x_241 x_256))) (= x_300 (select x_241 x_258))) (or (or (or (and (and (and (and (and (and (and (= x_252 0) (= x_250 (+ x_236 1))) ?v_5) ?v_6) (= x_254 x_253)) (= x_298 1)) (= x_255 (store x_241 x_253 2))) (= x_247 (store x_233 x_236 x_253))) (and (and (and (and (and (and (and (and (and (= x_252 1) ?v_7) ?v_5) ?v_6) ?v_8) ?v_9) (= x_257 x_256)) (= x_299 2)) (= x_246 x_256)) (= x_255 (store x_241 x_256 3)))) (and (and (and (and (and (and (and (and (and (= x_252 2) ?v_7) (= x_248 (+ x_234 1))) ?v_6) ?v_8) ?v_9) (= x_259 x_258)) (= x_300 3)) (or (not (<= x_237 12)) (= x_246 x_258))) (= x_255 (store x_241 x_258 1)))) (and (and (and (and (and (= x_252 3) ?v_8) ?v_5) ?v_6) (= x_255 x_241)) ?v_9))) (= x_237 (+ x_223 1))) (= x_301 (select x_227 x_239))) (= x_302 (select x_227 x_242))) (= x_303 (select x_227 x_244))) (or (or (or (and (and (and (and (and (and (and (= x_238 0) (= x_236 (+ x_222 1))) ?v_10) ?v_11) (= x_240 x_239)) (= x_301 1)) (= x_241 (store x_227 x_239 2))) (= x_233 (store x_219 x_222 x_239))) (and (and (and (and (and (and (and (and (and (= x_238 1) ?v_12) ?v_10) ?v_11) ?v_13) ?v_14) (= x_243 x_242)) (= x_302 2)) (= x_232 x_242)) (= x_241 (store x_227 x_242 3)))) (and (and (and (and (and (and (and (and (and (= x_238 2) ?v_12) (= x_234 (+ x_220 1))) ?v_11) ?v_13) ?v_14) (= x_245 x_244)) (= x_303 3)) (or (not (<= x_223 12)) (= x_232 x_244))) (= x_241 (store x_227 x_244 1)))) (and (and (and (and (and (= x_238 3) ?v_13) ?v_10) ?v_11) (= x_241 x_227)) ?v_14))) (= x_223 (+ x_209 1))) (= x_304 (select x_213 x_225))) (= x_305 (select x_213 x_228))) (= x_306 (select x_213 x_230))) (or (or (or (and (and (and (and (and (and (and (= x_224 0) (= x_222 (+ x_208 1))) ?v_15) ?v_16) (= x_226 x_225)) (= x_304 1)) (= x_227 (store x_213 x_225 2))) (= x_219 (store x_205 x_208 x_225))) (and (and (and (and (and (and (and (and (and (= x_224 1) ?v_17) ?v_15) ?v_16) ?v_18) ?v_19) (= x_229 x_228)) (= x_305 2)) (= x_218 x_228)) (= x_227 (store x_213 x_228 3)))) (and (and (and (and (and (and (and (and (and (= x_224 2) ?v_17) (= x_220 (+ x_206 1))) ?v_16) ?v_18) ?v_19) (= x_231 x_230)) (= x_306 3)) (or (not (<= x_209 12)) (= x_218 x_230))) (= x_227 (store x_213 x_230 1)))) (and (and (and (and (and (= x_224 3) ?v_18) ?v_15) ?v_16) (= x_227 x_213)) ?v_19))) (= x_209 (+ x_195 1))) (= x_307 (select x_199 x_211))) (= x_308 (select x_199 x_214))) (= x_309 (select x_199 x_216))) (or (or (or (and (and (and (and (and (and (and (= x_210 0) (= x_208 (+ x_194 1))) ?v_20) ?v_21) (= x_212 x_211)) (= x_307 1)) (= x_213 (store x_199 x_211 2))) (= x_205 (store x_191 x_194 x_211))) (and (and (and (and (and (and (and (and (and (= x_210 1) ?v_22) ?v_20) ?v_21) ?v_23) ?v_24) (= x_215 x_214)) (= x_308 2)) (= x_204 x_214)) (= x_213 (store x_199 x_214 3)))) (and (and (and (and (and (and (and (and (and (= x_210 2) ?v_22) (= x_206 (+ x_192 1))) ?v_21) ?v_23) ?v_24) (= x_217 x_216)) (= x_309 3)) (or (not (<= x_195 12)) (= x_204 x_216))) (= x_213 (store x_199 x_216 1)))) (and (and (and (and (and (= x_210 3) ?v_23) ?v_20) ?v_21) (= x_213 x_199)) ?v_24))) (= x_195 (+ x_181 1))) (= x_310 (select x_185 x_197))) (= x_311 (select x_185 x_200))) (= x_312 (select x_185 x_202))) (or (or (or (and (and (and (and (and (and (and (= x_196 0) (= x_194 (+ x_180 1))) ?v_25) ?v_26) (= x_198 x_197)) (= x_310 1)) (= x_199 (store x_185 x_197 2))) (= x_191 (store x_177 x_180 x_197))) (and (and (and (and (and (and (and (and (and (= x_196 1) ?v_27) ?v_25) ?v_26) ?v_28) ?v_29) (= x_201 x_200)) (= x_311 2)) (= x_190 x_200)) (= x_199 (store x_185 x_200 3)))) (and (and (and (and (and (and (and (and (and (= x_196 2) ?v_27) (= x_192 (+ x_178 1))) ?v_26) ?v_28) ?v_29) (= x_203 x_202)) (= x_312 3)) (or (not (<= x_181 12)) (= x_190 x_202))) (= x_199 (store x_185 x_202 1)))) (and (and (and (and (and (= x_196 3) ?v_28) ?v_25) ?v_26) (= x_199 x_185)) ?v_29))) (= x_181 (+ x_167 1))) (= x_313 (select x_171 x_183))) (= x_314 (select x_171 x_186))) (= x_315 (select x_171 x_188))) (or (or (or (and (and (and (and (and (and (and (= x_182 0) (= x_180 (+ x_166 1))) ?v_30) ?v_31) (= x_184 x_183)) (= x_313 1)) (= x_185 (store x_171 x_183 2))) (= x_177 (store x_163 x_166 x_183))) (and (and (and (and (and (and (and (and (and (= x_182 1) ?v_32) ?v_30) ?v_31) ?v_33) ?v_34) (= x_187 x_186)) (= x_314 2)) (= x_176 x_186)) (= x_185 (store x_171 x_186 3)))) (and (and (and (and (and (and (and (and (and (= x_182 2) ?v_32) (= x_178 (+ x_164 1))) ?v_31) ?v_33) ?v_34) (= x_189 x_188)) (= x_315 3)) (or (not (<= x_167 12)) (= x_176 x_188))) (= x_185 (store x_171 x_188 1)))) (and (and (and (and (and (= x_182 3) ?v_33) ?v_30) ?v_31) (= x_185 x_171)) ?v_34))) (= x_167 (+ x_153 1))) (= x_316 (select x_157 x_169))) (= x_317 (select x_157 x_172))) (= x_318 (select x_157 x_174))) (or (or (or (and (and (and (and (and (and (and (= x_168 0) (= x_166 (+ x_152 1))) ?v_35) ?v_36) (= x_170 x_169)) (= x_316 1)) (= x_171 (store x_157 x_169 2))) (= x_163 (store x_149 x_152 x_169))) (and (and (and (and (and (and (and (and (and (= x_168 1) ?v_37) ?v_35) ?v_36) ?v_38) ?v_39) (= x_173 x_172)) (= x_317 2)) (= x_162 x_172)) (= x_171 (store x_157 x_172 3)))) (and (and (and (and (and (and (and (and (and (= x_168 2) ?v_37) (= x_164 (+ x_150 1))) ?v_36) ?v_38) ?v_39) (= x_175 x_174)) (= x_318 3)) (or (not (<= x_153 12)) (= x_162 x_174))) (= x_171 (store x_157 x_174 1)))) (and (and (and (and (and (= x_168 3) ?v_38) ?v_35) ?v_36) (= x_171 x_157)) ?v_39))) (= x_153 (+ x_139 1))) (= x_319 (select x_143 x_155))) (= x_320 (select x_143 x_158))) (= x_321 (select x_143 x_160))) (or (or (or (and (and (and (and (and (and (and (= x_154 0) (= x_152 (+ x_138 1))) ?v_40) ?v_41) (= x_156 x_155)) (= x_319 1)) (= x_157 (store x_143 x_155 2))) (= x_149 (store x_135 x_138 x_155))) (and (and (and (and (and (and (and (and (and (= x_154 1) ?v_42) ?v_40) ?v_41) ?v_43) ?v_44) (= x_159 x_158)) (= x_320 2)) (= x_148 x_158)) (= x_157 (store x_143 x_158 3)))) (and (and (and (and (and (and (and (and (and (= x_154 2) ?v_42) (= x_150 (+ x_136 1))) ?v_41) ?v_43) ?v_44) (= x_161 x_160)) (= x_321 3)) (or (not (<= x_139 12)) (= x_148 x_160))) (= x_157 (store x_143 x_160 1)))) (and (and (and (and (and (= x_154 3) ?v_43) ?v_40) ?v_41) (= x_157 x_143)) ?v_44))) (= x_139 (+ x_125 1))) (= x_322 (select x_129 x_141))) (= x_323 (select x_129 x_144))) (= x_324 (select x_129 x_146))) (or (or (or (and (and (and (and (and (and (and (= x_140 0) (= x_138 (+ x_124 1))) ?v_45) ?v_46) (= x_142 x_141)) (= x_322 1)) (= x_143 (store x_129 x_141 2))) (= x_135 (store x_121 x_124 x_141))) (and (and (and (and (and (and (and (and (and (= x_140 1) ?v_47) ?v_45) ?v_46) ?v_48) ?v_49) (= x_145 x_144)) (= x_323 2)) (= x_134 x_144)) (= x_143 (store x_129 x_144 3)))) (and (and (and (and (and (and (and (and (and (= x_140 2) ?v_47) (= x_136 (+ x_122 1))) ?v_46) ?v_48) ?v_49) (= x_147 x_146)) (= x_324 3)) (or (not (<= x_125 12)) (= x_134 x_146))) (= x_143 (store x_129 x_146 1)))) (and (and (and (and (and (= x_140 3) ?v_48) ?v_45) ?v_46) (= x_143 x_129)) ?v_49))) (= x_125 (+ x_111 1))) (= x_325 (select x_115 x_127))) (= x_326 (select x_115 x_130))) (= x_327 (select x_115 x_132))) (or (or (or (and (and (and (and (and (and (and (= x_126 0) (= x_124 (+ x_110 1))) ?v_50) ?v_51) (= x_128 x_127)) (= x_325 1)) (= x_129 (store x_115 x_127 2))) (= x_121 (store x_107 x_110 x_127))) (and (and (and (and (and (and (and (and (and (= x_126 1) ?v_52) ?v_50) ?v_51) ?v_53) ?v_54) (= x_131 x_130)) (= x_326 2)) (= x_120 x_130)) (= x_129 (store x_115 x_130 3)))) (and (and (and (and (and (and (and (and (and (= x_126 2) ?v_52) (= x_122 (+ x_108 1))) ?v_51) ?v_53) ?v_54) (= x_133 x_132)) (= x_327 3)) (or (not (<= x_111 12)) (= x_120 x_132))) (= x_129 (store x_115 x_132 1)))) (and (and (and (and (and (= x_126 3) ?v_53) ?v_50) ?v_51) (= x_129 x_115)) ?v_54))) (= x_111 (+ x_97 1))) (= x_328 (select x_101 x_113))) (= x_329 (select x_101 x_116))) (= x_330 (select x_101 x_118))) (or (or (or (and (and (and (and (and (and (and (= x_112 0) (= x_110 (+ x_96 1))) ?v_55) ?v_56) (= x_114 x_113)) (= x_328 1)) (= x_115 (store x_101 x_113 2))) (= x_107 (store x_93 x_96 x_113))) (and (and (and (and (and (and (and (and (and (= x_112 1) ?v_57) ?v_55) ?v_56) ?v_58) ?v_59) (= x_117 x_116)) (= x_329 2)) (= x_106 x_116)) (= x_115 (store x_101 x_116 3)))) (and (and (and (and (and (and (and (and (and (= x_112 2) ?v_57) (= x_108 (+ x_94 1))) ?v_56) ?v_58) ?v_59) (= x_119 x_118)) (= x_330 3)) (or (not (<= x_97 12)) (= x_106 x_118))) (= x_115 (store x_101 x_118 1)))) (and (and (and (and (and (= x_112 3) ?v_58) ?v_55) ?v_56) (= x_115 x_101)) ?v_59))) (= x_97 (+ x_83 1))) (= x_331 (select x_87 x_99))) (= x_332 (select x_87 x_102))) (= x_333 (select x_87 x_104))) (or (or (or (and (and (and (and (and (and (and (= x_98 0) (= x_96 (+ x_82 1))) ?v_60) ?v_61) (= x_100 x_99)) (= x_331 1)) (= x_101 (store x_87 x_99 2))) (= x_93 (store x_79 x_82 x_99))) (and (and (and (and (and (and (and (and (and (= x_98 1) ?v_62) ?v_60) ?v_61) ?v_63) ?v_64) (= x_103 x_102)) (= x_332 2)) (= x_92 x_102)) (= x_101 (store x_87 x_102 3)))) (and (and (and (and (and (and (and (and (and (= x_98 2) ?v_62) (= x_94 (+ x_80 1))) ?v_61) ?v_63) ?v_64) (= x_105 x_104)) (= x_333 3)) (or (not (<= x_83 12)) (= x_92 x_104))) (= x_101 (store x_87 x_104 1)))) (and (and (and (and (and (= x_98 3) ?v_63) ?v_60) ?v_61) (= x_101 x_87)) ?v_64))) (= x_83 (+ x_69 1))) (= x_334 (select x_73 x_85))) (= x_335 (select x_73 x_88))) (= x_336 (select x_73 x_90))) (or (or (or (and (and (and (and (and (and (and (= x_84 0) (= x_82 (+ x_68 1))) ?v_65) ?v_66) (= x_86 x_85)) (= x_334 1)) (= x_87 (store x_73 x_85 2))) (= x_79 (store x_65 x_68 x_85))) (and (and (and (and (and (and (and (and (and (= x_84 1) ?v_67) ?v_65) ?v_66) ?v_68) ?v_69) (= x_89 x_88)) (= x_335 2)) (= x_78 x_88)) (= x_87 (store x_73 x_88 3)))) (and (and (and (and (and (and (and (and (and (= x_84 2) ?v_67) (= x_80 (+ x_66 1))) ?v_66) ?v_68) ?v_69) (= x_91 x_90)) (= x_336 3)) (or (not (<= x_69 12)) (= x_78 x_90))) (= x_87 (store x_73 x_90 1)))) (and (and (and (and (and (= x_84 3) ?v_68) ?v_65) ?v_66) (= x_87 x_73)) ?v_69))) (= x_69 (+ x_55 1))) (= x_337 (select x_59 x_71))) (= x_338 (select x_59 x_74))) (= x_339 (select x_59 x_76))) (or (or (or (and (and (and (and (and (and (and (= x_70 0) (= x_68 (+ x_54 1))) ?v_70) ?v_71) (= x_72 x_71)) (= x_337 1)) (= x_73 (store x_59 x_71 2))) (= x_65 (store x_51 x_54 x_71))) (and (and (and (and (and (and (and (and (and (= x_70 1) ?v_72) ?v_70) ?v_71) ?v_73) ?v_74) (= x_75 x_74)) (= x_338 2)) (= x_64 x_74)) (= x_73 (store x_59 x_74 3)))) (and (and (and (and (and (and (and (and (and (= x_70 2) ?v_72) (= x_66 (+ x_52 1))) ?v_71) ?v_73) ?v_74) (= x_77 x_76)) (= x_339 3)) (or (not (<= x_55 12)) (= x_64 x_76))) (= x_73 (store x_59 x_76 1)))) (and (and (and (and (and (= x_70 3) ?v_73) ?v_70) ?v_71) (= x_73 x_59)) ?v_74))) (= x_55 (+ x_41 1))) (= x_340 (select x_45 x_57))) (= x_341 (select x_45 x_60))) (= x_342 (select x_45 x_62))) (or (or (or (and (and (and (and (and (and (and (= x_56 0) (= x_54 (+ x_40 1))) ?v_75) ?v_76) (= x_58 x_57)) (= x_340 1)) (= x_59 (store x_45 x_57 2))) (= x_51 (store x_37 x_40 x_57))) (and (and (and (and (and (and (and (and (and (= x_56 1) ?v_77) ?v_75) ?v_76) ?v_78) ?v_79) (= x_61 x_60)) (= x_341 2)) (= x_50 x_60)) (= x_59 (store x_45 x_60 3)))) (and (and (and (and (and (and (and (and (and (= x_56 2) ?v_77) (= x_52 (+ x_38 1))) ?v_76) ?v_78) ?v_79) (= x_63 x_62)) (= x_342 3)) (or (not (<= x_41 12)) (= x_50 x_62))) (= x_59 (store x_45 x_62 1)))) (and (and (and (and (and (= x_56 3) ?v_78) ?v_75) ?v_76) (= x_59 x_45)) ?v_79))) (= x_41 (+ x_27 1))) (= x_343 (select x_31 x_43))) (= x_344 (select x_31 x_46))) (= x_345 (select x_31 x_48))) (or (or (or (and (and (and (and (and (and (and (= x_42 0) (= x_40 (+ x_26 1))) ?v_80) ?v_81) (= x_44 x_43)) (= x_343 1)) (= x_45 (store x_31 x_43 2))) (= x_37 (store x_23 x_26 x_43))) (and (and (and (and (and (and (and (and (and (= x_42 1) ?v_82) ?v_80) ?v_81) ?v_83) ?v_84) (= x_47 x_46)) (= x_344 2)) (= x_36 x_46)) (= x_45 (store x_31 x_46 3)))) (and (and (and (and (and (and (and (and (and (= x_42 2) ?v_82) (= x_38 (+ x_24 1))) ?v_81) ?v_83) ?v_84) (= x_49 x_48)) (= x_345 3)) (or (not (<= x_27 12)) (= x_36 x_48))) (= x_45 (store x_31 x_48 1)))) (and (and (and (and (and (= x_42 3) ?v_83) ?v_80) ?v_81) (= x_45 x_31)) ?v_84))) (= x_27 (+ x_13 1))) (= x_346 (select x_17 x_29))) (= x_347 (select x_17 x_32))) (= x_348 (select x_17 x_34))) (or (or (or (and (and (and (and (and (and (and (= x_28 0) (= x_26 (+ x_12 1))) ?v_85) ?v_86) (= x_30 x_29)) (= x_346 1)) (= x_31 (store x_17 x_29 2))) (= x_23 (store x_9 x_12 x_29))) (and (and (and (and (and (and (and (and (and (= x_28 1) ?v_87) ?v_85) ?v_86) ?v_88) ?v_89) (= x_33 x_32)) (= x_347 2)) (= x_22 x_32)) (= x_31 (store x_17 x_32 3)))) (and (and (and (and (and (and (and (and (and (= x_28 2) ?v_87) (= x_24 (+ x_10 1))) ?v_86) ?v_88) ?v_89) (= x_35 x_34)) (= x_348 3)) (or (not (<= x_13 12)) (= x_22 x_34))) (= x_31 (store x_17 x_34 1)))) (and (and (and (and (and (= x_28 3) ?v_88) ?v_85) ?v_86) (= x_31 x_17)) ?v_89))) (= x_13 (+ x_6 1))) (= x_349 (select x_2 x_15))) (= x_350 (select x_2 x_18))) (= x_351 (select x_2 x_20))) (or (or (or (and (and (and (and (and (and (and (= x_14 0) (= x_12 (+ x_1 1))) ?v_90) ?v_91) (= x_16 x_15)) (= x_349 1)) (= x_17 (store x_2 x_15 2))) (= x_9 (store x_7 x_1 x_15))) (and (and (and (and (and (and (and (and (and (= x_14 1) ?v_92) ?v_90) ?v_91) ?v_93) ?v_94) (= x_19 x_18)) (= x_350 2)) (= x_8 x_18)) (= x_17 (store x_2 x_18 3)))) (and (and (and (and (and (and (and (and (and (= x_14 2) ?v_92) (= x_10 (+ x_0 1))) ?v_91) ?v_93) ?v_94) (= x_21 x_20)) (= x_351 3)) (or (not (<= x_6 12)) (= x_8 x_20))) (= x_17 (store x_2 x_20 1)))) (and (and (and (and (and (= x_14 3) ?v_93) ?v_90) ?v_91) (= x_17 x_2)) ?v_94))) (= x_352 (select x_269 x_3))) (= x_353 (select x_269 x_4))) (= x_354 (select x_255 x_3))) (= x_355 (select x_255 x_4))) (= x_356 (select x_241 x_3))) (= x_357 (select x_241 x_4))) (= x_358 (select x_227 x_3))) (= x_359 (select x_227 x_4))) (= x_360 (select x_213 x_3))) (= x_361 (select x_213 x_4))) (= x_362 (select x_199 x_3))) (= x_363 (select x_199 x_4))) (= x_364 (select x_185 x_3))) (= x_365 (select x_185 x_4))) (= x_366 (select x_171 x_3))) (= x_367 (select x_171 x_4))) (= x_368 (select x_157 x_3))) (= x_369 (select x_157 x_4))) (= x_370 (select x_143 x_3))) (= x_371 (select x_143 x_4))) (= x_372 (select x_129 x_3))) (= x_373 (select x_129 x_4))) (= x_374 (select x_115 x_3))) (= x_375 (select x_115 x_4))) (= x_376 (select x_101 x_3))) (= x_377 (select x_101 x_4))) (= x_378 (select x_87 x_3))) (= x_379 (select x_87 x_4))) (= x_380 (select x_73 x_3))) (= x_381 (select x_73 x_4))) (= x_382 (select x_59 x_3))) (= x_383 (select x_59 x_4))) (= x_384 (select x_45 x_3))) (= x_385 (select x_45 x_4))) (= x_386 (select x_31 x_3))) (= x_387 (select x_31 x_4))) (= x_388 (select x_17 x_3))) (= x_389 (select x_17 x_4))) (= x_390 ?v_95)) (= x_391 ?v_96)) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (= x_352 3) (= x_353 3)) (and (= x_354 3) (= x_355 3))) (and (= x_356 3) (= x_357 3))) (and (= x_358 3) (= x_359 3))) (and (= x_360 3) (= x_361 3))) (and (= x_362 3) (= x_363 3))) (and (= x_364 3) (= x_365 3))) (and (= x_366 3) (= x_367 3))) (and (= x_368 3) (= x_369 3))) (and (= x_370 3) (= x_371 3))) (and (= x_372 3) (= x_373 3))) (and (= x_374 3) (= x_375 3))) (and (= x_376 3) (= x_377 3))) (and (= x_378 3) (= x_379 3))) (and (= x_380 3) (= x_381 3))) (and (= x_382 3) (= x_383 3))) (and (= x_384 3) (= x_385 3))) (and (= x_386 3) (= x_387 3))) (and (= x_388 3) (= x_389 3))) (and (= x_390 3) (= x_391 3))))))
(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
(exit)
