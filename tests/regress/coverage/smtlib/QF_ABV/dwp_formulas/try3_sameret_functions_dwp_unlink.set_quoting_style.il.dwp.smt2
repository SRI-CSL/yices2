(set-logic QF_ABV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun mem_35_241 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_235 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_231 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_229 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun t_228 () (_ BitVec 1))
(declare-fun t_227 () (_ BitVec 1))
(declare-fun t_226 () (_ BitVec 1))
(declare-fun t_225 () (_ BitVec 1))
(declare-fun t_224 () (_ BitVec 1))
(declare-fun t_223 () (_ BitVec 1))
(declare-fun t_222 () (_ BitVec 1))
(declare-fun t_221 () (_ BitVec 1))
(declare-fun t_220 () (_ BitVec 1))
(declare-fun t_219 () (_ BitVec 1))
(declare-fun t_218 () (_ BitVec 1))
(declare-fun t_217 () (_ BitVec 1))
(declare-fun t_216 () (_ BitVec 1))
(declare-fun t_215 () (_ BitVec 1))
(declare-fun t_214 () (_ BitVec 1))
(declare-fun t_213 () (_ BitVec 1))
(declare-fun t_212 () (_ BitVec 1))
(declare-fun t_211 () (_ BitVec 1))
(declare-fun t_210 () (_ BitVec 1))
(declare-fun t_209 () (_ BitVec 1))
(declare-fun t_208 () (_ BitVec 1))
(declare-fun t_207 () (_ BitVec 1))
(declare-fun t_206 () (_ BitVec 1))
(declare-fun t_205 () (_ BitVec 1))
(declare-fun t_204 () (_ BitVec 1))
(declare-fun ra_final_56_203 () (_ BitVec 32))
(declare-fun T_32t1_1220_200 () (_ BitVec 32))
(declare-fun T_32t2_1224_196 () (_ BitVec 32))
(declare-fun T_32t3_1230_189 () (_ BitVec 32))
(declare-fun T_32t1_1228_188 () (_ BitVec 32))
(declare-fun ra_final_56_186 () (_ BitVec 32))
(declare-fun T_32t1_1208_183 () (_ BitVec 32))
(declare-fun T_32t2_1212_179 () (_ BitVec 32))
(declare-fun T_32t3_1218_171 () (_ BitVec 32))
(declare-fun T_32t1_1216_170 () (_ BitVec 32))
(declare-fun ra_final_56_156 () (_ BitVec 32))
(declare-fun T_1t0_1231_140 () (_ BitVec 1))
(declare-fun T_32t5_1236_139 () (_ BitVec 32))
(declare-fun R_ZF_13_134 () (_ BitVec 1))
(declare-fun T_32t3_1244_112 () (_ BitVec 32))
(declare-fun T_32t1_1242_111 () (_ BitVec 32))
(declare-fun T_32t2_1248_105 () (_ BitVec 32))
(declare-fun ra0_57_102 () (_ BitVec 32))
(declare-fun R_ESP_1_66 () (_ BitVec 32))
(declare-fun R_EBP_0_57 () (_ BitVec 32))
(assert (let ((?v_0 (bvadd T_32t2_1248_105 (_ bv4 32))) (?v_1 (bvadd T_32t2_1248_105 (_ bv12 32)))) (= (_ bv1 1) (bvand (bvand (ite (= t_204 (ite (= ra_final_56_156 ra_final_56_186) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_205 (ite (= ra_final_56_186 T_32t1_1208_183) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_206 (ite (= T_32t1_1208_183 (bvor (bvor (bvor (concat (_ bv0 24) (select mem_35_229 (bvadd T_32t2_1212_179 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_229 (bvadd T_32t2_1212_179 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select mem_35_229 (bvadd T_32t2_1212_179 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select mem_35_229 (bvadd T_32t2_1212_179 (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_207 (ite (= T_32t2_1212_179 ?v_0) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_208 (ite (= mem_35_229 (store (store (store (store mem_35_231 (bvadd (_ bv134528192 32) (_ bv3 32)) ((_ extract 7 0) (bvlshr T_32t3_1218_171 (_ bv24 32)))) (bvadd (_ bv134528192 32) (_ bv2 32)) ((_ extract 7 0) (bvlshr T_32t3_1218_171 (_ bv16 32)))) (bvadd (_ bv134528192 32) (_ bv1 32)) ((_ extract 7 0) (bvlshr T_32t3_1218_171 (_ bv8 32)))) (bvadd (_ bv134528192 32) (_ bv0 32)) ((_ extract 7 0) T_32t3_1218_171))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_209 (ite (= T_32t3_1218_171 (bvor (bvor (bvor (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1216_170 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1216_170 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1216_170 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1216_170 (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_210 (ite (= T_32t1_1216_170 ?v_1) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_211 T_1t0_1231_140) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_212 (ite (= ra_final_56_156 ra_final_56_203) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_213 (ite (= ra_final_56_203 T_32t1_1220_200) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_214 (ite (= T_32t1_1220_200 (bvor (bvor (bvor (concat (_ bv0 24) (select mem_35_235 (bvadd T_32t2_1224_196 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_235 (bvadd T_32t2_1224_196 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select mem_35_235 (bvadd T_32t2_1224_196 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select mem_35_235 (bvadd T_32t2_1224_196 (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_215 (ite (= T_32t2_1224_196 ?v_0) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_216 (ite (= mem_35_235 (store (store (store (store mem_35_231 (bvadd T_32t3_1244_112 (_ bv3 32)) ((_ extract 7 0) (bvlshr T_32t3_1230_189 (_ bv24 32)))) (bvadd T_32t3_1244_112 (_ bv2 32)) ((_ extract 7 0) (bvlshr T_32t3_1230_189 (_ bv16 32)))) (bvadd T_32t3_1244_112 (_ bv1 32)) ((_ extract 7 0) (bvlshr T_32t3_1230_189 (_ bv8 32)))) (bvadd T_32t3_1244_112 (_ bv0 32)) ((_ extract 7 0) T_32t3_1230_189))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_217 (ite (= T_32t3_1230_189 (bvor (bvor (bvor (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1228_188 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1228_188 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1228_188 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1228_188 (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_218 (ite (= T_32t1_1228_188 ?v_1) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_219 (bvnot T_1t0_1231_140)) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_220 (bvor (bvand t_211 (bvand t_210 (bvand t_209 (bvand t_208 (bvand t_207 (bvand t_206 (bvand t_205 t_204))))))) (bvand t_219 (bvand t_218 (bvand t_217 (bvand t_216 (bvand t_215 (bvand t_214 (bvand t_213 t_212))))))))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_221 (ite (= T_1t0_1231_140 ((_ extract 0 0) T_32t5_1236_139)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_222 (ite (= T_32t5_1236_139 (concat (_ bv0 31) R_ZF_13_134)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_223 (ite (= R_ZF_13_134 (ite (= T_32t3_1244_112 (_ bv0 32)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_224 (ite (= T_32t3_1244_112 (bvor (bvor (bvor (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1242_111 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1242_111 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1242_111 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select mem_35_231 (bvadd T_32t1_1242_111 (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_225 (ite (= T_32t1_1242_111 (bvadd T_32t2_1248_105 (_ bv8 32))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_226 (ite (= mem_35_231 (store (store (store (store mem_35_241 (bvadd T_32t2_1248_105 (_ bv3 32)) ((_ extract 7 0) (bvlshr R_EBP_0_57 (_ bv24 32)))) (bvadd T_32t2_1248_105 (_ bv2 32)) ((_ extract 7 0) (bvlshr R_EBP_0_57 (_ bv16 32)))) (bvadd T_32t2_1248_105 (_ bv1 32)) ((_ extract 7 0) (bvlshr R_EBP_0_57 (_ bv8 32)))) (bvadd T_32t2_1248_105 (_ bv0 32)) ((_ extract 7 0) R_EBP_0_57))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= t_227 (ite (= T_32t2_1248_105 (bvsub R_ESP_1_66 (_ bv4 32))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_228 (ite (= ra0_57_102 (bvor (bvor (bvor (concat (_ bv0 24) (select mem_35_241 (bvadd R_ESP_1_66 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_241 (bvadd R_ESP_1_66 (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select mem_35_241 (bvadd R_ESP_1_66 (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select mem_35_241 (bvadd R_ESP_1_66 (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)))))))))))))))))))))))))) (bvand (bvnot (_ bv0 1)) (bvand (bvand t_228 (bvand t_227 (bvand t_226 (bvand t_225 (bvand t_224 (bvand t_223 (bvand t_222 (bvand t_221 t_220)))))))) (ite (= ra0_57_102 ra_final_56_156) (_ bv1 1) (_ bv0 1))))))))
(check-sat)
(set-option :regular-output-channel "NUL")
(get-model)
(exit)
