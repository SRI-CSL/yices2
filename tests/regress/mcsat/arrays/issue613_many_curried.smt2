; Stress test for MCSAT curried function model building.
;
; Model reconstruction uses an int_hmap from function-id to function-value.
; With the default initial size of 32 and a 0.6 load factor, the table grows
; at ~19 entries. Each curried head here contributes two distinct function-ids
; (the outer array and the inner array returned by selecting from it), so with
; 25 arrays we reach ~50 entries and force at least two resizes during model
; construction. A stale int_hmap_pair_t pointer held across a recursive
; get_function_value would be dereferenced after safe_free / realloc, which
; previously caused a use-after-free crash or silent model corruption.

(set-option :produce-models true)
(set-logic QF_ALIA)

(declare-fun a1  () (Array Int (Array Int Int)))
(declare-fun a2  () (Array Int (Array Int Int)))
(declare-fun a3  () (Array Int (Array Int Int)))
(declare-fun a4  () (Array Int (Array Int Int)))
(declare-fun a5  () (Array Int (Array Int Int)))
(declare-fun a6  () (Array Int (Array Int Int)))
(declare-fun a7  () (Array Int (Array Int Int)))
(declare-fun a8  () (Array Int (Array Int Int)))
(declare-fun a9  () (Array Int (Array Int Int)))
(declare-fun a10 () (Array Int (Array Int Int)))
(declare-fun a11 () (Array Int (Array Int Int)))
(declare-fun a12 () (Array Int (Array Int Int)))
(declare-fun a13 () (Array Int (Array Int Int)))
(declare-fun a14 () (Array Int (Array Int Int)))
(declare-fun a15 () (Array Int (Array Int Int)))
(declare-fun a16 () (Array Int (Array Int Int)))
(declare-fun a17 () (Array Int (Array Int Int)))
(declare-fun a18 () (Array Int (Array Int Int)))
(declare-fun a19 () (Array Int (Array Int Int)))
(declare-fun a20 () (Array Int (Array Int Int)))
(declare-fun a21 () (Array Int (Array Int Int)))
(declare-fun a22 () (Array Int (Array Int Int)))
(declare-fun a23 () (Array Int (Array Int Int)))
(declare-fun a24 () (Array Int (Array Int Int)))
(declare-fun a25 () (Array Int (Array Int Int)))

(assert (= (select (select a1  1)  1)  101))
(assert (= (select (select a2  2)  2)  102))
(assert (= (select (select a3  3)  3)  103))
(assert (= (select (select a4  4)  4)  104))
(assert (= (select (select a5  5)  5)  105))
(assert (= (select (select a6  6)  6)  106))
(assert (= (select (select a7  7)  7)  107))
(assert (= (select (select a8  8)  8)  108))
(assert (= (select (select a9  9)  9)  109))
(assert (= (select (select a10 10) 10) 110))
(assert (= (select (select a11 11) 11) 111))
(assert (= (select (select a12 12) 12) 112))
(assert (= (select (select a13 13) 13) 113))
(assert (= (select (select a14 14) 14) 114))
(assert (= (select (select a15 15) 15) 115))
(assert (= (select (select a16 16) 16) 116))
(assert (= (select (select a17 17) 17) 117))
(assert (= (select (select a18 18) 18) 118))
(assert (= (select (select a19 19) 19) 119))
(assert (= (select (select a20 20) 20) 120))
(assert (= (select (select a21 21) 21) 121))
(assert (= (select (select a22 22) 22) 122))
(assert (= (select (select a23 23) 23) 123))
(assert (= (select (select a24 24) 24) 124))
(assert (= (select (select a25 25) 25) 125))

(check-sat)

; Probe a handful of values to exercise model evaluation on the reconstructed
; curried functions. The specific values are constrained to the literal in the
; corresponding assertion.
(get-value ((select (select a1  1)  1)))
(get-value ((select (select a13 13) 13)))
(get-value ((select (select a25 25) 25)))
