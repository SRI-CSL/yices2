; Command:
; > yices_smt2_mt --incremental

(set-logic QF_UFBV)
(declare-fun theory20_len ((_ BitVec 64)) (_ BitVec 64)); theory len
(declare-fun theory21_safe ((_ BitVec 64)) Bool); theory safe
(declare-fun theory22_nullterm ((_ BitVec 64)) Bool); theory nullterm
(declare-fun theory23_symbol ((_ BitVec 64)) Bool); theory symbol
(declare-fun theory24_typeof ((_ BitVec 64)) (_ BitVec 64)); theory typeof
(declare-fun theory25_tailof ((_ BitVec 64)) (_ BitVec 64)); theory tailof
; : /home/aep/proj/zz/modules/vec/src/lib.zz:19
; : /home/aep/proj/zz/modules/slice/src/slice.zz:3
; : /home/aep/proj/zz/modules/vec/src/lib.zz:205
; : /home/aep/proj/zz/modules/vec/src/lib.zz:217
(declare-fun var30___vec__iter__t0 () (_ BitVec 64))
(declare-fun var31_true__t0 () Bool)
(assert
  (= var31_true__t0 (theory21_safe var30___vec__iter__t0) )
)

(assert
  var31_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:5
; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:11
(declare-fun theory33___slice__mut_slice__integrity ((_ BitVec 64)) Bool); theory ::slice::mut_slice::integrity
; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:168
(declare-fun var34___slice__mut_slice__append_obj__t0 () (_ BitVec 64))
(declare-fun var35_true__t0 () Bool)
(assert
  (= var35_true__t0 (theory21_safe var34___slice__mut_slice__append_obj__t0) )
)

(assert
  var35_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:18
; : /home/aep/proj/zz/modules/err/src/lib.zz:66
(declare-fun var37___err__backtrace__t0 () (_ BitVec 64))
(declare-fun var38_true__t0 () Bool)
(assert
  (= var38_true__t0 (theory21_safe var37___err__backtrace__t0) )
)

(assert
  var38_true__t0
)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:23
; : /home/aep/proj/zz/modules/pool/src/lib.zz:86
(declare-fun var40___pool__free_bytes__t0 () (_ BitVec 64))
(declare-fun var41_true__t0 () Bool)
(assert
  (= var41_true__t0 (theory21_safe var40___pool__free_bytes__t0) )
)

(assert
  var41_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:94
(declare-fun var42___slice__mut_slice__append_cstr__t0 () (_ BitVec 64))
(declare-fun var43_true__t0 () Bool)
(assert
  (= var43_true__t0 (theory21_safe var42___slice__mut_slice__append_cstr__t0) )
)

(assert
  var43_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:153
(declare-fun var44___slice__mut_slice__push64__t0 () (_ BitVec 64))
(declare-fun var45_true__t0 () Bool)
(assert
  (= var45_true__t0 (theory21_safe var44___slice__mut_slice__push64__t0) )
)

(assert
  var45_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:11
; : /home/aep/proj/zz/modules/slice/src/slice.zz:8
(declare-fun theory47___slice__slice__integrity ((_ BitVec 64)) Bool); theory ::slice::slice::integrity
; : /home/aep/proj/zz/modules/buffer/src/lib.zz:17
(declare-fun theory48___buffer__integrity ((_ BitVec 64)) Bool); theory ::buffer::integrity
; : /home/aep/proj/zz/modules/buffer/src/lib.zz:199
(declare-fun var49___buffer__append_slice__t0 () (_ BitVec 64))
(declare-fun var50_true__t0 () Bool)
(assert
  (= var50_true__t0 (theory21_safe var49___buffer__append_slice__t0) )
)

(assert
  var50_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:75
(declare-fun var51___slice__slice__split__t0 () (_ BitVec 64))
(declare-fun var52_true__t0 () Bool)
(assert
  (= var52_true__t0 (theory21_safe var51___slice__slice__split__t0) )
)

(assert
  var52_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:43
(declare-fun var53___slice__slice__empty__t0 () (_ BitVec 64))
(declare-fun var54_true__t0 () Bool)
(assert
  (= var54_true__t0 (theory21_safe var53___slice__slice__empty__t0) )
)

(assert
  var54_true__t0
)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:23
; : /home/aep/proj/zz/modules/pool/src/lib.zz:21
(declare-fun theory55___pool__continuous ((_ BitVec 64)) Bool); theory ::pool::continuous
; : /home/aep/proj/zz/modules/pool/src/lib.zz:42
(declare-fun var56___pool__make__t0 () (_ BitVec 64))
(declare-fun var57_true__t0 () Bool)
(assert
  (= var57_true__t0 (theory21_safe var56___pool__make__t0) )
)

(assert
  var57_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:147
(declare-fun var58___slice__slice__atoi__t0 () (_ BitVec 64))
(declare-fun var59_true__t0 () Bool)
(assert
  (= var59_true__t0 (theory21_safe var58___slice__slice__atoi__t0) )
)

(assert
  var59_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:225
(declare-fun var60___vec__next__t0 () (_ BitVec 64))
(declare-fun var61_true__t0 () Bool)
(assert
  (= var61_true__t0 (theory21_safe var60___vec__next__t0) )
)

(assert
  var61_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:195
(declare-fun var62___err__eprintf__t0 () (_ BitVec 64))
(declare-fun var63_true__t0 () Bool)
(assert
  (= var63_true__t0 (theory21_safe var62___err__eprintf__t0) )
)

(assert
  var63_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:11
(declare-fun theory64___err__checked ((_ BitVec 64)) Bool); theory ::err::checked
; : /home/aep/proj/zz/modules/err/src/lib.zz:72
(declare-fun var65___err__fail_with_errno__t0 () (_ BitVec 64))
(declare-fun var66_true__t0 () Bool)
(assert
  (= var66_true__t0 (theory21_safe var65___err__fail_with_errno__t0) )
)

(assert
  var66_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:107
(declare-fun var67___slice__slice__sub__t0 () (_ BitVec 64))
(declare-fun var68_true__t0 () Bool)
(assert
  (= var68_true__t0 (theory21_safe var67___slice__slice__sub__t0) )
)

(assert
  var68_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:19
; : /home/aep/proj/zz/modules/vec/src/lib.zz:8
(declare-fun theory69___vec__item ((_ BitVec 64)) (_ BitVec 64)); theory ::vec::item
; : /home/aep/proj/zz/modules/vec/src/lib.zz:11
(declare-fun theory70___vec__integrity ((_ BitVec 64)) Bool); theory ::vec::integrity
; : /home/aep/proj/zz/modules/vec/src/lib.zz:179
(declare-fun var71___vec__get__t0 () (_ BitVec 64))
(declare-fun var72_true__t0 () Bool)
(assert
  (= var72_true__t0 (theory21_safe var71___vec__get__t0) )
)

(assert
  var72_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:49
(declare-fun var73___slice__mut_slice__space__t0 () (_ BitVec 64))
(declare-fun var74_true__t0 () Bool)
(assert
  (= var74_true__t0 (theory21_safe var73___slice__mut_slice__space__t0) )
)

(assert
  var74_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:189
(declare-fun var75___err__elog__t0 () (_ BitVec 64))
(declare-fun var76_true__t0 () Bool)
(assert
  (= var76_true__t0 (theory21_safe var75___err__elog__t0) )
)

(assert
  var76_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:27
(declare-fun var77___buffer__make__t0 () (_ BitVec 64))
(declare-fun var78_true__t0 () Bool)
(assert
  (= var78_true__t0 (theory21_safe var77___buffer__make__t0) )
)

(assert
  var78_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:181
(declare-fun var79___buffer__append_cstr__t0 () (_ BitVec 64))
(declare-fun var80_true__t0 () Bool)
(assert
  (= var80_true__t0 (theory21_safe var79___buffer__append_cstr__t0) )
)

(assert
  var80_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:196
(declare-fun var81___vec__delete__t0 () (_ BitVec 64))
(declare-fun var82_true__t0 () Bool)
(assert
  (= var82_true__t0 (theory21_safe var81___vec__delete__t0) )
)

(assert
  var82_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:5
; : /home/aep/proj/zz/modules/buffer/src/lib.zz:113
(declare-fun var83___buffer__as_mut_slice__t0 () (_ BitVec 64))
(declare-fun var84_true__t0 () Bool)
(assert
  (= var84_true__t0 (theory21_safe var83___buffer__as_mut_slice__t0) )
)

(assert
  var84_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:51
(declare-fun var85___slice__slice__make__t0 () (_ BitVec 64))
(declare-fun var86_true__t0 () Bool)
(assert
  (= var86_true__t0 (theory21_safe var85___slice__slice__make__t0) )
)

(assert
  var86_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:14
(declare-fun var87___slice__slice__eq__t0 () (_ BitVec 64))
(declare-fun var88_true__t0 () Bool)
(assert
  (= var88_true__t0 (theory21_safe var87___slice__slice__eq__t0) )
)

(assert
  var88_true__t0
)

; : /home/aep/proj/zz/modules/log/src/lib.zz:68
(declare-fun var89___log__info__t0 () (_ BitVec 64))
(declare-fun var90_true__t0 () Bool)
(assert
  (= var90_true__t0 (theory21_safe var89___log__info__t0) )
)

(assert
  var90_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:11
; : /home/aep/proj/zz/modules/err/src/lib.zz:18
; : /home/aep/proj/zz/modules/buffer/src/lib.zz:326
(declare-fun var91___buffer__ends_with_cstr__t0 () (_ BitVec 64))
(declare-fun var92_true__t0 () Bool)
(assert
  (= var92_true__t0 (theory21_safe var91___buffer__ends_with_cstr__t0) )
)

(assert
  var92_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:88
(declare-fun var93___buffer__cstr__t0 () (_ BitVec 64))
(declare-fun var94_true__t0 () Bool)
(assert
  (= var94_true__t0 (theory21_safe var93___buffer__cstr__t0) )
)

(assert
  var94_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:108
(declare-fun var95___slice__mut_slice__push__t0 () (_ BitVec 64))
(declare-fun var96_true__t0 () Bool)
(assert
  (= var96_true__t0 (theory21_safe var95___slice__mut_slice__push__t0) )
)

(assert
  var96_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:138
(declare-fun var97___slice__mut_slice__push32__t0 () (_ BitVec 64))
(declare-fun var98_true__t0 () Bool)
(assert
  (= var98_true__t0 (theory21_safe var97___slice__mut_slice__push32__t0) )
)

(assert
  var98_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:50
(declare-fun var99___err__check__t0 () (_ BitVec 64))
(declare-fun var100_true__t0 () Bool)
(assert
  (= var100_true__t0 (theory21_safe var99___err__check__t0) )
)

(assert
  var100_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:135
(declare-fun var101___err__fail__t0 () (_ BitVec 64))
(declare-fun var102_true__t0 () Bool)
(assert
  (= var102_true__t0 (theory21_safe var101___err__fail__t0) )
)

(assert
  var102_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:37
(declare-fun var103___err__ignore__t0 () (_ BitVec 64))
(declare-fun var104_true__t0 () Bool)
(assert
  (= var104_true__t0 (theory21_safe var103___err__ignore__t0) )
)

(assert
  var104_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:122
(declare-fun var105___buffer__push__t0 () (_ BitVec 64))
(declare-fun var106_true__t0 () Bool)
(assert
  (= var106_true__t0 (theory21_safe var105___buffer__push__t0) )
)

(assert
  var106_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:216
(declare-fun var107___buffer__append_bytes__t0 () (_ BitVec 64))
(declare-fun var108_true__t0 () Bool)
(assert
  (= var108_true__t0 (theory21_safe var107___buffer__append_bytes__t0) )
)

(assert
  var108_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:245
(declare-fun var109___buffer__vformat__t0 () (_ BitVec 64))
(declare-fun var110_true__t0 () Bool)
(assert
  (= var110_true__t0 (theory21_safe var109___buffer__vformat__t0) )
)

(assert
  var110_true__t0
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:30
(declare-fun var111___mem__zero__t0 () (_ BitVec 64))
(declare-fun var112_true__t0 () Bool)
(assert
  (= var112_true__t0 (theory21_safe var111___mem__zero__t0) )
)

(assert
  var112_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:277
(declare-fun var113___err__assert_safe__t0 () (_ BitVec 64))
(declare-fun var114_true__t0 () Bool)
(assert
  (= var114_true__t0 (theory21_safe var113___err__assert_safe__t0) )
)

(assert
  var114_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:55
(declare-fun var115___vec__make_with_pool__t0 () (_ BitVec 64))
(declare-fun var116_true__t0 () Bool)
(assert
  (= var116_true__t0 (theory21_safe var115___vec__make_with_pool__t0) )
)

(assert
  var116_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:56
(declare-fun var117___slice__mut_slice__append_slice__t0 () (_ BitVec 64))
(declare-fun var118_true__t0 () Bool)
(assert
  (= var118_true__t0 (theory21_safe var117___slice__mut_slice__append_slice__t0) )
)

(assert
  var118_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:33
(declare-fun var119___slice__slice__eq_bytes__t0 () (_ BitVec 64))
(declare-fun var120_true__t0 () Bool)
(assert
  (= var120_true__t0 (theory21_safe var119___slice__slice__eq_bytes__t0) )
)

(assert
  var120_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:407
(declare-fun var121___buffer__split__t0 () (_ BitVec 64))
(declare-fun var122_true__t0 () Bool)
(assert
  (= var122_true__t0 (theory21_safe var121___buffer__split__t0) )
)

(assert
  var122_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:201
(declare-fun var123___err__to_str__t0 () (_ BitVec 64))
(declare-fun var124_true__t0 () Bool)
(assert
  (= var124_true__t0 (theory21_safe var123___err__to_str__t0) )
)

(assert
  var124_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:161
(declare-fun var125___vec__push_i__t0 () (_ BitVec 64))
(declare-fun var126_true__t0 () Bool)
(assert
  (= var126_true__t0 (theory21_safe var125___vec__push_i__t0) )
)

(assert
  var126_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:344
(declare-fun var127___buffer__fgets__t0 () (_ BitVec 64))
(declare-fun var128_true__t0 () Bool)
(assert
  (= var128_true__t0 (theory21_safe var127___buffer__fgets__t0) )
)

(assert
  var128_true__t0
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:3
(declare-fun var129___mem__copy__t0 () (_ BitVec 64))
(declare-fun var130_true__t0 () Bool)
(assert
  (= var130_true__t0 (theory21_safe var129___mem__copy__t0) )
)

(assert
  var130_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:121
(declare-fun var131___vec__push__t0 () (_ BitVec 64))
(declare-fun var132_true__t0 () Bool)
(assert
  (= var132_true__t0 (theory21_safe var131___vec__push__t0) )
)

(assert
  var132_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:360
(declare-fun var133___buffer__substr__t0 () (_ BitVec 64))
(declare-fun var134_true__t0 () Bool)
(assert
  (= var134_true__t0 (theory21_safe var133___buffer__substr__t0) )
)

(assert
  var134_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/slice.zz:24
(declare-fun var135___slice__slice__eq_cstr__t0 () (_ BitVec 64))
(declare-fun var136_true__t0 () Bool)
(assert
  (= var136_true__t0 (theory21_safe var135___slice__slice__eq_cstr__t0) )
)

(assert
  var136_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:20
(declare-fun var137___slice__mut_slice__make__t0 () (_ BitVec 64))
(declare-fun var138_true__t0 () Bool)
(assert
  (= var138_true__t0 (theory21_safe var137___slice__mut_slice__make__t0) )
)

(assert
  var138_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:139
(declare-fun var139___buffer__pop__t0 () (_ BitVec 64))
(declare-fun var140_true__t0 () Bool)
(assert
  (= var140_true__t0 (theory21_safe var139___buffer__pop__t0) )
)

(assert
  var140_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:97
(declare-fun var141___buffer__as_slice__t0 () (_ BitVec 64))
(declare-fun var142_true__t0 () Bool)
(assert
  (= var142_true__t0 (theory21_safe var141___buffer__as_slice__t0) )
)

(assert
  var142_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:232
(declare-fun var143___buffer__format__t0 () (_ BitVec 64))
(declare-fun var144_true__t0 () Bool)
(assert
  (= var144_true__t0 (theory21_safe var143___buffer__format__t0) )
)

(assert
  var144_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:32
(declare-fun var145___vec__make__t0 () (_ BitVec 64))
(declare-fun var146_true__t0 () Bool)
(assert
  (= var146_true__t0 (theory21_safe var145___vec__make__t0) )
)

(assert
  var146_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:8
; : /home/aep/proj/zz/modules/buffer/src/lib.zz:39
(declare-fun var147___buffer__from_cstr__t0 () (_ BitVec 64))
(declare-fun var148_true__t0 () Bool)
(assert
  (= var148_true__t0 (theory21_safe var147___buffer__from_cstr__t0) )
)

(assert
  var148_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:59
(declare-fun var149___buffer__from_slice__t0 () (_ BitVec 64))
(declare-fun var150_true__t0 () Bool)
(assert
  (= var150_true__t0 (theory21_safe var149___buffer__from_slice__t0) )
)

(assert
  var150_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:71
(declare-fun var151___buffer__clear__t0 () (_ BitVec 64))
(declare-fun var152_true__t0 () Bool)
(assert
  (= var152_true__t0 (theory21_safe var151___buffer__clear__t0) )
)

(assert
  var152_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:170
(declare-fun var153___err__abort__t0 () (_ BitVec 64))
(declare-fun var154_true__t0 () Bool)
(assert
  (= var154_true__t0 (theory21_safe var153___err__abort__t0) )
)

(assert
  var154_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:11
; : /home/aep/proj/zz/modules/buffer/src/lib.zz:81
(declare-fun var155___buffer__slen__t0 () (_ BitVec 64))
(declare-fun var156_true__t0 () Bool)
(assert
  (= var156_true__t0 (theory21_safe var155___buffer__slen__t0) )
)

(assert
  var156_true__t0
)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:17
(declare-fun theory157___pool__member ((_ BitVec 64) (_ BitVec 64)) Bool); theory ::pool::member
; : /home/aep/proj/zz/modules/pool/src/lib.zz:152
(declare-fun var158___pool__malloc__t0 () (_ BitVec 64))
(declare-fun var159_true__t0 () Bool)
(assert
  (= var159_true__t0 (theory21_safe var158___pool__malloc__t0) )
)

(assert
  var159_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:36
(declare-fun var160___slice__mut_slice__as_slice__t0 () (_ BitVec 64))
(declare-fun var161_true__t0 () Bool)
(assert
  (= var161_true__t0 (theory21_safe var160___slice__mut_slice__as_slice__t0) )
)

(assert
  var161_true__t0
)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:134
(declare-fun var162___pool__copy__t0 () (_ BitVec 64))
(declare-fun var163_true__t0 () Bool)
(assert
  (= var163_true__t0 (theory21_safe var162___pool__copy__t0) )
)

(assert
  var163_true__t0
)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:117
(declare-fun var164___pool__alloc__t0 () (_ BitVec 64))
(declare-fun var165_true__t0 () Bool)
(assert
  (= var165_true__t0 (theory21_safe var164___pool__alloc__t0) )
)

(assert
  var165_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:26
(declare-fun var166___err__make__t0 () (_ BitVec 64))
(declare-fun var167_true__t0 () Bool)
(assert
  (= var167_true__t0 (theory21_safe var166___err__make__t0) )
)

(assert
  var167_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:123
(declare-fun var168___slice__mut_slice__push16__t0 () (_ BitVec 64))
(declare-fun var169_true__t0 () Bool)
(assert
  (= var169_true__t0 (theory21_safe var168___slice__mut_slice__push16__t0) )
)

(assert
  var169_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:150
(declare-fun var170___vec__push_b__t0 () (_ BitVec 64))
(declare-fun var171_true__t0 () Bool)
(assert
  (= var171_true__t0 (theory21_safe var170___vec__push_b__t0) )
)

(assert
  var171_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:49
(declare-fun var172___buffer__from_bytes__t0 () (_ BitVec 64))
(declare-fun var173_true__t0 () Bool)
(assert
  (= var173_true__t0 (theory21_safe var172___buffer__from_bytes__t0) )
)

(assert
  var173_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:310
(declare-fun var174___buffer__starts_with_cstr__t0 () (_ BitVec 64))
(declare-fun var175_true__t0 () Bool)
(assert
  (= var175_true__t0 (theory21_safe var174___buffer__starts_with_cstr__t0) )
)

(assert
  var175_true__t0
)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:254
(declare-fun var176___pool__free__t0 () (_ BitVec 64))
(declare-fun var177_true__t0 () Bool)
(assert
  (= var177_true__t0 (theory21_safe var176___pool__free__t0) )
)

(assert
  var177_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:71
(declare-fun var178___vec__grow__t0 () (_ BitVec 64))
(declare-fun var179_true__t0 () Bool)
(assert
  (= var179_true__t0 (theory21_safe var178___vec__grow__t0) )
)

(assert
  var179_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:103
(declare-fun var180___err__fail_with_system_error__t0 () (_ BitVec 64))
(declare-fun var181_true__t0 () Bool)
(assert
  (= var181_true__t0 (theory21_safe var180___err__fail_with_system_error__t0) )
)

(assert
  var181_true__t0
)

; : /home/aep/proj/zz/modules/slice/src/mut_slice.zz:75
(declare-fun var182___slice__mut_slice__append_bytes__t0 () (_ BitVec 64))
(declare-fun var183_true__t0 () Bool)
(assert
  (= var183_true__t0 (theory21_safe var182___slice__mut_slice__append_bytes__t0) )
)

(assert
  var183_true__t0
)

; : /home/aep/proj/zz/modules/err/src/lib.zz:294
(declare-fun var184___err__fail_with_win32__t0 () (_ BitVec 64))
(declare-fun var185_true__t0 () Bool)
(assert
  (= var185_true__t0 (theory21_safe var184___err__fail_with_win32__t0) )
)

(assert
  var185_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:274
(declare-fun var186___buffer__eq_cstr__t0 () (_ BitVec 64))
(declare-fun var187_true__t0 () Bool)
(assert
  (= var187_true__t0 (theory21_safe var186___buffer__eq_cstr__t0) )
)

(assert
  var187_true__t0
)

; : /home/aep/proj/zz/modules/buffer/src/lib.zz:172
(declare-fun var188___buffer__available__t0 () (_ BitVec 64))
(declare-fun var189_true__t0 () Bool)
(assert
  (= var189_true__t0 (theory21_safe var188___buffer__available__t0) )
)

(assert
  var189_true__t0
)

;


;----------------------------------------------
;function ::vec::grow
;----------------------------------------------

(push 1)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:71
; : /home/aep/proj/zz/modules/vec/src/lib.zz:71
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var190_self__t0 () (_ BitVec 64))
(declare-fun var191_safe_self___t0 () Bool)
(assert
  (= var191_safe_self___t0 (theory21_safe var190_self__t0) )
)

(assert (! var191_safe_self___t0 :named A0))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:72
; call of ::vec::integrity
; : /home/aep/proj/zz/modules/vec/src/lib.zz:72
; : /home/aep/proj/zz/modules/vec/src/lib.zz:72
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; theory_expression
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; type_params_into_ssa deref(var190_self).items
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
(declare-fun var193_deref_var190_self__items__t0 () (_ BitVec 64))
(declare-fun var194_len_deref_var190_self__items___t0 () (_ BitVec 64))
(assert
  (= var194_len_deref_var190_self__items___t0 (theory20_len var193_deref_var190_self__items__t0) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; type_params_into_ssa deref(var190_self).capacity
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
(declare-fun var196_infix_expression__t0 () Bool)
(declare-fun var195_deref_var190_self__capacity__t0 () (_ BitVec 64))
(assert
  (=  var196_infix_expression__t0 (= var194_len_deref_var190_self__items___t0 var195_deref_var190_self__capacity__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; type_params_into_ssa deref(var190_self).owned
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
(declare-fun var197_deref_var190_self__owned__t0 () (_ BitVec 64))
(declare-fun var198_len_deref_var190_self__owned___t0 () (_ BitVec 64))
(assert
  (= var198_len_deref_var190_self__owned___t0 (theory20_len var197_deref_var190_self__owned__t0) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
(declare-fun var199_infix_expression__t0 () Bool)
(assert
  (=  var199_infix_expression__t0 (= var198_len_deref_var190_self__owned___t0 var195_deref_var190_self__capacity__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
(declare-fun var200_infix_expression__t0 () Bool)
(assert
  (=  var200_infix_expression__t0 (and var196_infix_expression__t0 var199_infix_expression__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; type_params_into_ssa deref(var190_self).count
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
(declare-fun var202_infix_expression__t0 () Bool)
(declare-fun var201_deref_var190_self__count__t0 () (_ BitVec 64))
(assert
  (=  var202_infix_expression__t0 (bvule var201_deref_var190_self__count__t0 var195_deref_var190_self__capacity__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
(declare-fun var203_infix_expression__t0 () Bool)
(assert
  (=  var203_infix_expression__t0 (and var200_infix_expression__t0 var202_infix_expression__t0))
)

; end of theory_expression
(assert (! var203_infix_expression__t0 :named A1))(check-sat)

; type_params_into_ssa deref(var190_self)
; : /home/aep/proj/zz/modules/vec/src/lib.zz:71
; type_params_into_ssa deref(var190_self).pool
(declare-fun var205_deref_var190_self__pool_pmem__t0 () (_ BitVec 64))
(declare-fun var206_true__t0 () Bool)
(assert
  (= var206_true__t0 (theory21_safe var205_deref_var190_self__pool_pmem__t0) )
)

(assert
  var206_true__t0
)

; type_params_into_ssa deref(var190_self).pool.pmem
(declare-fun var204_deref_var190_self__pool__t0 () (_ BitVec 64))
(declare-fun var207_len_deref_var190_self__pool_pmem_____tailof_deref_var190_self__pool___t0 () (_ BitVec 64))
(assert
  (= var207_len_deref_var190_self__pool_pmem_____tailof_deref_var190_self__pool___t0 (theory25_tailof var204_deref_var190_self__pool__t0) )
)

(assert
  (= var207_len_deref_var190_self__pool_pmem_____tailof_deref_var190_self__pool___t0 (theory20_len var205_deref_var190_self__pool_pmem__t0) )
)

(declare-fun var192_deref_var190_self___t0 () (_ BitVec 64))
(declare-fun var208_tailof_deref_var190_self__pool_____tailof_deref_var190_self____t0 () (_ BitVec 64))
(assert
  (= var208_tailof_deref_var190_self__pool_____tailof_deref_var190_self____t0 (theory25_tailof var192_deref_var190_self___t0) )
)

(assert
  (= var208_tailof_deref_var190_self__pool_____tailof_deref_var190_self____t0 (theory25_tailof var204_deref_var190_self__pool__t0) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:71
; : /home/aep/proj/zz/modules/vec/src/lib.zz:76
; type_params_into_ssa nucap
; : /home/aep/proj/zz/modules/vec/src/lib.zz:76
; : /home/aep/proj/zz/modules/vec/src/lib.zz:76
; : /home/aep/proj/zz/modules/vec/src/lib.zz:76
; : /home/aep/proj/zz/modules/vec/src/lib.zz:76
; literal expr
(declare-fun var211_literal_Unsigned_2___t0 () (_ BitVec 64))
(assert
  (= var211_literal_Unsigned_2___t0 (_ bv2 64))

)

(declare-fun var212_implicit_coercion_of_literal_Unsigned_2___t0 () (_ BitVec 64))
(assert (! (= var212_implicit_coercion_of_literal_Unsigned_2___t0 var211_literal_Unsigned_2___t0) :named A2)); : /home/aep/proj/zz/modules/vec/src/lib.zz:76
(declare-fun var213_infix_expression__t0 () (_ BitVec 64))
(assert
  (=  var213_infix_expression__t0 (bvmul var195_deref_var190_self__capacity__t0 var212_implicit_coercion_of_literal_Unsigned_2___t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:76
(declare-fun var214_safe_infix_expression_____safe_nucap___t0 () Bool)
(assert
  (= var214_safe_infix_expression_____safe_nucap___t0 (theory21_safe var213_infix_expression__t0) )
)

(declare-fun var210_nucap__t1 () (_ BitVec 64))
(assert
  (= var214_safe_infix_expression_____safe_nucap___t0 (theory21_safe var210_nucap__t1) )
)

(declare-fun var215_nullterm_infix_expression_____nullterm_nucap___t0 () Bool)
(assert
  (= var215_nullterm_infix_expression_____nullterm_nucap___t0 (theory22_nullterm var213_infix_expression__t0) )
)

(assert
  (= var215_nullterm_infix_expression_____nullterm_nucap___t0 (theory22_nullterm var210_nucap__t1) )
)

; type_params_into_ssa nucap
(declare-fun var210_nucap__t0 () (_ BitVec 64))
(assert
  (= var210_nucap__t1  (ite true var213_infix_expression__t0 var210_nucap__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:77
; : /home/aep/proj/zz/modules/vec/src/lib.zz:77
; : /home/aep/proj/zz/modules/vec/src/lib.zz:77
; literal expr
(declare-fun var216_literal_Unsigned_2___t0 () (_ BitVec 64))
(assert
  (= var216_literal_Unsigned_2___t0 (_ bv2 64))

)

(declare-fun var217_implicit_coercion_of_literal_Unsigned_2___t0 () (_ BitVec 64))
(assert (! (= var217_implicit_coercion_of_literal_Unsigned_2___t0 var216_literal_Unsigned_2___t0) :named A3)); : /home/aep/proj/zz/modules/vec/src/lib.zz:77
(declare-fun var218_infix_expression__t0 () Bool)
(assert
  (=  var218_infix_expression__t0 (bvult var210_nucap__t1 var217_implicit_coercion_of_literal_Unsigned_2___t0))
)

(check-sat)

(get-value (

  var218_infix_expression__t0

) )

;  = "true"
(push 1)

(assert
  (not (= var218_infix_expression__t0 true))
)

(check-sat)

(pop 1)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:77
; : /home/aep/proj/zz/modules/vec/src/lib.zz:78
; : /home/aep/proj/zz/modules/vec/src/lib.zz:78
; literal expr
(declare-fun var219_literal_Unsigned_2___t0 () (_ BitVec 64))
(assert
  (= var219_literal_Unsigned_2___t0 (_ bv2 64))

)

(declare-fun var220_implicit_coercion_of_literal_Unsigned_2___t0 () (_ BitVec 64))
(assert (! (= var220_implicit_coercion_of_literal_Unsigned_2___t0 var219_literal_Unsigned_2___t0) :named A4)); : /home/aep/proj/zz/modules/vec/src/lib.zz:78
(declare-fun var221_safe_implicit_coercion_of_literal_Unsigned_2______safe_nucap___t0 () Bool)
(assert
  (= var221_safe_implicit_coercion_of_literal_Unsigned_2______safe_nucap___t0 (theory21_safe var220_implicit_coercion_of_literal_Unsigned_2___t0) )
)

(declare-fun var210_nucap__t2 () (_ BitVec 64))
(assert
  (= var221_safe_implicit_coercion_of_literal_Unsigned_2______safe_nucap___t0 (theory21_safe var210_nucap__t2) )
)

(declare-fun var222_nullterm_implicit_coercion_of_literal_Unsigned_2______nullterm_nucap___t0 () Bool)
(assert
  (= var222_nullterm_implicit_coercion_of_literal_Unsigned_2______nullterm_nucap___t0 (theory22_nullterm var220_implicit_coercion_of_literal_Unsigned_2___t0) )
)

(assert
  (= var222_nullterm_implicit_coercion_of_literal_Unsigned_2______nullterm_nucap___t0 (theory22_nullterm var210_nucap__t2) )
)

; type_params_into_ssa nucap
(assert
  (= var210_nucap__t2  (ite var218_infix_expression__t0 var220_implicit_coercion_of_literal_Unsigned_2___t0 var210_nucap__t1)  )
)

; end branch
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; type_params_into_ssa numem
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; call
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; call of ::pool::malloc
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
(declare-fun var225_addressof_deref_var190_self__pool___t0 () (_ BitVec 64))
(declare-fun var226_len_addressof_deref_var190_self__pool____t0 () (_ BitVec 64))
(assert
  (= var226_len_addressof_deref_var190_self__pool____t0 (theory20_len var225_addressof_deref_var190_self__pool___t0) )
)

(assert
  (= var226_len_addressof_deref_var190_self__pool____t0 (_ bv1 64))

)

(assert
  (= var225_addressof_deref_var190_self__pool___t0 (_ bv204 64))

)

(declare-fun var227_true__t0 () Bool)
(assert
  (= var227_true__t0 (theory21_safe var225_addressof_deref_var190_self__pool___t0) )
)

(assert
  var227_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
(declare-fun var229_infix_expression__t0 () (_ BitVec 64))
(declare-fun var228_unsafe_expression__t0 () (_ BitVec 64))
(assert
  (=  var229_infix_expression__t0 (bvmul var228_unsafe_expression__t0 var210_nucap__t2))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
(declare-fun var230_addressof_deref_var190_self__pool___t0 () (_ BitVec 64))
(declare-fun var231_len_addressof_deref_var190_self__pool____t0 () (_ BitVec 64))
(assert
  (= var231_len_addressof_deref_var190_self__pool____t0 (theory20_len var230_addressof_deref_var190_self__pool___t0) )
)

(assert
  (= var231_len_addressof_deref_var190_self__pool____t0 (_ bv1 64))

)

(assert
  (= var230_addressof_deref_var190_self__pool___t0 (_ bv204 64))

)

(declare-fun var232_true__t0 () Bool)
(assert
  (= var232_true__t0 (theory21_safe var230_addressof_deref_var190_self__pool___t0) )
)

(assert
  var232_true__t0
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
(declare-fun var234_infix_expression__t0 () (_ BitVec 64))
(declare-fun var233_unsafe_expression__t0 () (_ BitVec 64))
(assert
  (=  var234_infix_expression__t0 (bvmul var233_unsafe_expression__t0 var210_nucap__t2))
)

;callsite_assert
(push 1)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:152
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var235_safe_addressof_deref_var190_self__pool____t0 () Bool)
(assert
  (= var235_safe_addressof_deref_var190_self__pool____t0 (theory21_safe var230_addressof_deref_var190_self__pool___t0) )
)

(push 1)

(assert
  (and true (or (not var235_safe_addressof_deref_var190_self__pool____t0 ) ))

)

(check-sat)

; unsat / pass
(pop 1)

;end of callsite_assert
(pop 1)

(declare-fun var235_safe_addressof_deref_var190_self__pool____t0 () Bool)
; borrows after call
; 204 to temporal +1 because of function borrow
(declare-fun var204_deref_var190_self__pool__t1 () (_ BitVec 64))
(assert
  (= var204_deref_var190_self__pool__t1  (ite true var204_deref_var190_self__pool__t1 var204_deref_var190_self__pool__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:71
; end of borrows after call
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
; callsite effects
(declare-fun var236_return_value_of___pool__malloc__t0 () (_ BitVec 64))
(declare-fun var238_safe_return_value_of___pool__malloc_____safe_return___t0 () Bool)
(assert
  (= var238_safe_return_value_of___pool__malloc_____safe_return___t0 (theory21_safe var236_return_value_of___pool__malloc__t0) )
)

(declare-fun var237_return__t1 () (_ BitVec 64))
(assert
  (= var238_safe_return_value_of___pool__malloc_____safe_return___t0 (theory21_safe var237_return__t1) )
)

(declare-fun var239_nullterm_return_value_of___pool__malloc_____nullterm_return___t0 () Bool)
(assert
  (= var239_nullterm_return_value_of___pool__malloc_____nullterm_return___t0 (theory22_nullterm var236_return_value_of___pool__malloc__t0) )
)

(assert
  (= var239_nullterm_return_value_of___pool__malloc_____nullterm_return___t0 (theory22_nullterm var237_return__t1) )
)

; type_params_into_ssa return
(declare-fun var237_return__t0 () (_ BitVec 64))
(assert
  (= var237_return__t1  (ite true var236_return_value_of___pool__malloc__t0 var237_return__t0)  )
)

; : /home/aep/proj/zz/modules/pool/src/lib.zz:153
; call of ::pool::member
; : /home/aep/proj/zz/modules/pool/src/lib.zz:153
; : /home/aep/proj/zz/modules/pool/src/lib.zz:153
; : /home/aep/proj/zz/modules/pool/src/lib.zz:153
; collecting theory invocation arguments
; : /home/aep/proj/zz/modules/pool/src/lib.zz:153
; : /home/aep/proj/zz/modules/pool/src/lib.zz:153
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/pool/src/lib.zz:153
(declare-fun var240___pool__member_return__addressof_deref_var190_self__pool____t0 () Bool)
(assert
  (= var240___pool__member_return__addressof_deref_var190_self__pool____t0 (theory157___pool__member var237_return__t1 var230_addressof_deref_var190_self__pool___t0) )
)

(assert (! var240___pool__member_return__addressof_deref_var190_self__pool____t0 :named A5))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
(declare-fun var241_safe_return_____safe_return_value_of___pool__malloc___t0 () Bool)
(assert
  (= var241_safe_return_____safe_return_value_of___pool__malloc___t0 (theory21_safe var237_return__t1) )
)

(declare-fun var236_return_value_of___pool__malloc__t1 () (_ BitVec 64))
(assert
  (= var241_safe_return_____safe_return_value_of___pool__malloc___t0 (theory21_safe var236_return_value_of___pool__malloc__t1) )
)

(declare-fun var242_nullterm_return_____nullterm_return_value_of___pool__malloc___t0 () Bool)
(assert
  (= var242_nullterm_return_____nullterm_return_value_of___pool__malloc___t0 (theory22_nullterm var237_return__t1) )
)

(assert
  (= var242_nullterm_return_____nullterm_return_value_of___pool__malloc___t0 (theory22_nullterm var236_return_value_of___pool__malloc__t1) )
)

; type_params_into_ssa return value of ::pool::malloc
(assert
  (= var236_return_value_of___pool__malloc__t1  (ite true var237_return__t1 var236_return_value_of___pool__malloc__t0)  )
)

; end of callsite effects
; : /home/aep/proj/zz/modules/vec/src/lib.zz:81
(declare-fun var243_safe_return_value_of___pool__malloc_____safe_numem___t0 () Bool)
(assert
  (= var243_safe_return_value_of___pool__malloc_____safe_numem___t0 (theory21_safe var236_return_value_of___pool__malloc__t1) )
)

(declare-fun var223_numem__t1 () (_ BitVec 64))
(assert
  (= var243_safe_return_value_of___pool__malloc_____safe_numem___t0 (theory21_safe var223_numem__t1) )
)

(declare-fun var244_nullterm_return_value_of___pool__malloc_____nullterm_numem___t0 () Bool)
(assert
  (= var244_nullterm_return_value_of___pool__malloc_____nullterm_numem___t0 (theory22_nullterm var236_return_value_of___pool__malloc__t1) )
)

(assert
  (= var244_nullterm_return_value_of___pool__malloc_____nullterm_numem___t0 (theory22_nullterm var223_numem__t1) )
)

; type_params_into_ssa numem
(declare-fun var245_implicit_cast_of_return_value_of___pool__malloc__t0 () (_ BitVec 64))
(assert (! (= var245_implicit_cast_of_return_value_of___pool__malloc__t0 var236_return_value_of___pool__malloc__t1) :named A6))(declare-fun var223_numem__t0 () (_ BitVec 64))
(assert
  (= var223_numem__t1  (ite true var245_implicit_cast_of_return_value_of___pool__malloc__t0 var223_numem__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:82
; : /home/aep/proj/zz/modules/vec/src/lib.zz:82
; : /home/aep/proj/zz/modules/vec/src/lib.zz:82
; literal expr
(declare-fun var246_literal_Unsigned_0___t0 () (_ BitVec 64))
(assert
  (= var246_literal_Unsigned_0___t0 (_ bv0 64))

)

(declare-fun var247_implicit_coercion_of_literal_Unsigned_0___t0 () (_ BitVec 64))
(assert (! (= var247_implicit_coercion_of_literal_Unsigned_0___t0 var246_literal_Unsigned_0___t0) :named A7)); : /home/aep/proj/zz/modules/vec/src/lib.zz:82
(declare-fun var248_infix_expression__t0 () Bool)
(assert
  (=  var248_infix_expression__t0 (= var223_numem__t1 var247_implicit_coercion_of_literal_Unsigned_0___t0))
)

(check-sat)

(get-value (

  var248_infix_expression__t0

) )

;  = "false"
(push 1)

(assert
  (not (= var248_infix_expression__t0 false))
)

(check-sat)

(pop 1)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:82
; : /home/aep/proj/zz/modules/vec/src/lib.zz:83
; literal expr
(declare-fun var249_literal_Unsigned_0___t0 () Bool)
(assert
  (not var249_literal_Unsigned_0___t0)
)

; type_params_into_ssa return
(declare-fun var209_return__t1 () Bool)
(declare-fun var209_return__t0 () Bool)
(assert
  (= var209_return__t1  (ite var248_infix_expression__t0 var249_literal_Unsigned_0___t0 var209_return__t0)  )
)

;model check
(push 1)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:73
; call of ::vec::integrity
; : /home/aep/proj/zz/modules/vec/src/lib.zz:73
; : /home/aep/proj/zz/modules/vec/src/lib.zz:73
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; theory_expression
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
(declare-fun var250_len_deref_var190_self__items___t0 () (_ BitVec 64))
(assert
  (= var250_len_deref_var190_self__items___t0 (theory20_len var193_deref_var190_self__items__t0) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
(declare-fun var251_infix_expression__t0 () Bool)
(assert
  (=  var251_infix_expression__t0 (= var250_len_deref_var190_self__items___t0 var195_deref_var190_self__capacity__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
(declare-fun var252_len_deref_var190_self__owned___t0 () (_ BitVec 64))
(assert
  (= var252_len_deref_var190_self__owned___t0 (theory20_len var197_deref_var190_self__owned__t0) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
(declare-fun var253_infix_expression__t0 () Bool)
(assert
  (=  var253_infix_expression__t0 (= var252_len_deref_var190_self__owned___t0 var195_deref_var190_self__capacity__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:12
(declare-fun var254_infix_expression__t0 () Bool)
(assert
  (=  var254_infix_expression__t0 (and var251_infix_expression__t0 var253_infix_expression__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
; : /home/aep/proj/zz/modules/vec/src/lib.zz:14
(declare-fun var255_infix_expression__t0 () Bool)
(assert
  (=  var255_infix_expression__t0 (bvule var201_deref_var190_self__count__t0 var195_deref_var190_self__capacity__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:13
(declare-fun var256_infix_expression__t0 () Bool)
(assert
  (=  var256_infix_expression__t0 (and var254_infix_expression__t0 var255_infix_expression__t0))
)

; end of theory_expression
(push 1)

(assert
  (and var248_infix_expression__t0 (or (not var256_infix_expression__t0 ) ))

)

(check-sat)

; unsat / pass
(pop 1)

;end of model check
(pop 1)

(declare-fun var250_len_deref_var190_self__items___t0 () (_ BitVec 64))
(declare-fun var252_len_deref_var190_self__owned___t0 () (_ BitVec 64))
; end branch
; branch returned. the rest of the function only happens if the condition leading to return never happened
; (not var248_infix_expression__t0)
(assert
  (not var248_infix_expression__t0)
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:86
; type_params_into_ssa prev_memsize
; : /home/aep/proj/zz/modules/vec/src/lib.zz:86
; : /home/aep/proj/zz/modules/vec/src/lib.zz:86
; : /home/aep/proj/zz/modules/vec/src/lib.zz:86
; : /home/aep/proj/zz/modules/vec/src/lib.zz:86
; : /home/aep/proj/zz/modules/vec/src/lib.zz:86
(declare-fun var259_infix_expression__t0 () (_ BitVec 64))
(declare-fun var258_unsafe_expression__t0 () (_ BitVec 64))
(assert
  (=  var259_infix_expression__t0 (bvmul var258_unsafe_expression__t0 var195_deref_var190_self__capacity__t0))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:86
(declare-fun var260_safe_infix_expression_____safe_prev_memsize___t0 () Bool)
(assert
  (= var260_safe_infix_expression_____safe_prev_memsize___t0 (theory21_safe var259_infix_expression__t0) )
)

(declare-fun var257_prev_memsize__t1 () (_ BitVec 64))
(assert
  (= var260_safe_infix_expression_____safe_prev_memsize___t0 (theory21_safe var257_prev_memsize__t1) )
)

(declare-fun var261_nullterm_infix_expression_____nullterm_prev_memsize___t0 () Bool)
(assert
  (= var261_nullterm_infix_expression_____nullterm_prev_memsize___t0 (theory22_nullterm var259_infix_expression__t0) )
)

(assert
  (= var261_nullterm_infix_expression_____nullterm_prev_memsize___t0 (theory22_nullterm var257_prev_memsize__t1) )
)

; type_params_into_ssa prev_memsize
(declare-fun var257_prev_memsize__t0 () (_ BitVec 64))
(assert
  (= var257_prev_memsize__t1  (ite true var259_infix_expression__t0 var257_prev_memsize__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:87
; type_params_into_ssa new_memsize
; : /home/aep/proj/zz/modules/vec/src/lib.zz:87
; : /home/aep/proj/zz/modules/vec/src/lib.zz:87
; : /home/aep/proj/zz/modules/vec/src/lib.zz:87
; : /home/aep/proj/zz/modules/vec/src/lib.zz:87
(declare-fun var264_infix_expression__t0 () (_ BitVec 64))
(declare-fun var263_unsafe_expression__t0 () (_ BitVec 64))
(assert
  (=  var264_infix_expression__t0 (bvmul var263_unsafe_expression__t0 var210_nucap__t2))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:87
(declare-fun var265_safe_infix_expression_____safe_new_memsize___t0 () Bool)
(assert
  (= var265_safe_infix_expression_____safe_new_memsize___t0 (theory21_safe var264_infix_expression__t0) )
)

(declare-fun var262_new_memsize__t1 () (_ BitVec 64))
(assert
  (= var265_safe_infix_expression_____safe_new_memsize___t0 (theory21_safe var262_new_memsize__t1) )
)

(declare-fun var266_nullterm_infix_expression_____nullterm_new_memsize___t0 () Bool)
(assert
  (= var266_nullterm_infix_expression_____nullterm_new_memsize___t0 (theory22_nullterm var264_infix_expression__t0) )
)

(assert
  (= var266_nullterm_infix_expression_____nullterm_new_memsize___t0 (theory22_nullterm var262_new_memsize__t1) )
)

; type_params_into_ssa new_memsize
(declare-fun var262_new_memsize__t0 () (_ BitVec 64))
(assert
  (= var262_new_memsize__t1  (ite true var264_infix_expression__t0 var262_new_memsize__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:88
; type_params_into_ssa prev_mem
; : /home/aep/proj/zz/modules/vec/src/lib.zz:88
; : /home/aep/proj/zz/modules/vec/src/lib.zz:88
; : /home/aep/proj/zz/modules/vec/src/lib.zz:88
; : /home/aep/proj/zz/modules/vec/src/lib.zz:88
(declare-fun var268_cast_of_deref_var190_self__items__t0 () (_ BitVec 64))
(assert (! (= var268_cast_of_deref_var190_self__items__t0 var193_deref_var190_self__items__t0) :named A8)); : /home/aep/proj/zz/modules/vec/src/lib.zz:88
(declare-fun var269_safe_cast_of_deref_var190_self__items_____safe_prev_mem___t0 () Bool)
(assert
  (= var269_safe_cast_of_deref_var190_self__items_____safe_prev_mem___t0 (theory21_safe var268_cast_of_deref_var190_self__items__t0) )
)

(declare-fun var267_prev_mem__t1 () (_ BitVec 64))
(assert
  (= var269_safe_cast_of_deref_var190_self__items_____safe_prev_mem___t0 (theory21_safe var267_prev_mem__t1) )
)

(declare-fun var270_nullterm_cast_of_deref_var190_self__items_____nullterm_prev_mem___t0 () Bool)
(assert
  (= var270_nullterm_cast_of_deref_var190_self__items_____nullterm_prev_mem___t0 (theory22_nullterm var268_cast_of_deref_var190_self__items__t0) )
)

(assert
  (= var270_nullterm_cast_of_deref_var190_self__items_____nullterm_prev_mem___t0 (theory22_nullterm var267_prev_mem__t1) )
)

; type_params_into_ssa prev_mem
(declare-fun var267_prev_mem__t0 () (_ BitVec 64))
(assert
  (= var267_prev_mem__t1  (ite true var268_cast_of_deref_var190_self__items__t0 var267_prev_mem__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:89
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:89
; call of safe
; : /home/aep/proj/zz/modules/vec/src/lib.zz:89
; : /home/aep/proj/zz/modules/vec/src/lib.zz:89
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:89
(declare-fun var271_safe_numem___t0 () Bool)
(assert
  (= var271_safe_numem___t0 (theory21_safe var223_numem__t1) )
)

(assert (! var271_safe_numem___t0 :named A9))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:89
(declare-fun var272_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var272_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:90
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:90
; call of safe
; : /home/aep/proj/zz/modules/vec/src/lib.zz:90
; : /home/aep/proj/zz/modules/vec/src/lib.zz:90
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:90
(declare-fun var273_safe_prev_mem___t0 () Bool)
(assert
  (= var273_safe_prev_mem___t0 (theory21_safe var267_prev_mem__t1) )
)

(assert (! var273_safe_prev_mem___t0 :named A10))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:90
(declare-fun var274_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var274_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
(declare-fun var275_len_numem___t0 () (_ BitVec 64))
(assert
  (= var275_len_numem___t0 (theory20_len var223_numem__t1) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
(declare-fun var276_infix_expression__t0 () Bool)
(assert
  (=  var276_infix_expression__t0 (bvugt var275_len_numem___t0 var257_prev_memsize__t1))
)

(assert (! var276_infix_expression__t0 :named A11))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:91
(declare-fun var277_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var277_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
(declare-fun var278_len_prev_mem___t0 () (_ BitVec 64))
(assert
  (= var278_len_prev_mem___t0 (theory20_len var267_prev_mem__t1) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
(declare-fun var279_infix_expression__t0 () Bool)
(assert
  (=  var279_infix_expression__t0 (= var278_len_prev_mem___t0 var257_prev_memsize__t1))
)

(assert (! var279_infix_expression__t0 :named A12))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:92
(declare-fun var280_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var280_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; call of ::mem::copy
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
;callsite_assert
(push 1)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:3
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var281_safe_numem___t0 () Bool)
(assert
  (= var281_safe_numem___t0 (theory21_safe var223_numem__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:3
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var282_safe_prev_mem___t0 () Bool)
(assert
  (= var282_safe_prev_mem___t0 (theory21_safe var267_prev_mem__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; call of len
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
(declare-fun var283_len_numem___t0 () (_ BitVec 64))
(assert
  (= var283_len_numem___t0 (theory20_len var223_numem__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
(declare-fun var284_infix_expression__t0 () Bool)
(assert
  (=  var284_infix_expression__t0 (bvuge var283_len_numem___t0 var257_prev_memsize__t1))
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; call of len
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
(declare-fun var285_len_prev_mem___t0 () (_ BitVec 64))
(assert
  (= var285_len_prev_mem___t0 (theory20_len var267_prev_mem__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
(declare-fun var286_infix_expression__t0 () Bool)
(assert
  (=  var286_infix_expression__t0 (bvuge var285_len_prev_mem___t0 var257_prev_memsize__t1))
)

(push 1)

(assert
  (and true (or (not var281_safe_numem___t0 ) (not var282_safe_prev_mem___t0 ) (not var284_infix_expression__t0 ) (not var286_infix_expression__t0 ) ))

)

(check-sat)

; unsat / pass
(pop 1)

;end of callsite_assert
(pop 1)

(declare-fun var281_safe_numem___t0 () Bool)
(declare-fun var282_safe_prev_mem___t0 () Bool)
(declare-fun var283_len_numem___t0 () (_ BitVec 64))
(declare-fun var285_len_prev_mem___t0 () (_ BitVec 64))
; borrows after call
; end of borrows after call
; : /home/aep/proj/zz/modules/vec/src/lib.zz:93
; callsite effects
; end of callsite effects
; : /home/aep/proj/zz/modules/vec/src/lib.zz:95
; type_params_into_ssa prev_owned
; : /home/aep/proj/zz/modules/vec/src/lib.zz:95
; : /home/aep/proj/zz/modules/vec/src/lib.zz:95
(declare-fun var289_unsafe_expression__t0 () (_ BitVec 64))
(declare-fun var290_safe_unsafe_expression_____safe_prev_owned___t0 () Bool)
(assert
  (= var290_safe_unsafe_expression_____safe_prev_owned___t0 (theory21_safe var289_unsafe_expression__t0) )
)

(declare-fun var288_prev_owned__t1 () (_ BitVec 64))
(assert
  (= var290_safe_unsafe_expression_____safe_prev_owned___t0 (theory21_safe var288_prev_owned__t1) )
)

(declare-fun var291_nullterm_unsafe_expression_____nullterm_prev_owned___t0 () Bool)
(assert
  (= var291_nullterm_unsafe_expression_____nullterm_prev_owned___t0 (theory22_nullterm var289_unsafe_expression__t0) )
)

(assert
  (= var291_nullterm_unsafe_expression_____nullterm_prev_owned___t0 (theory22_nullterm var288_prev_owned__t1) )
)

; type_params_into_ssa prev_owned
(declare-fun var288_prev_owned__t0 () (_ BitVec 64))
(assert
  (= var288_prev_owned__t1  (ite true var289_unsafe_expression__t0 var288_prev_owned__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:96
; type_params_into_ssa prev_owned_size
; : /home/aep/proj/zz/modules/vec/src/lib.zz:96
; : /home/aep/proj/zz/modules/vec/src/lib.zz:96
; : /home/aep/proj/zz/modules/vec/src/lib.zz:96
; : /home/aep/proj/zz/modules/vec/src/lib.zz:96
(declare-fun var294_infix_expression__t0 () (_ BitVec 64))
(declare-fun var293_unsafe_expression__t0 () (_ BitVec 64))
(assert
  (=  var294_infix_expression__t0 (bvmul var293_unsafe_expression__t0 var210_nucap__t2))
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:96
(declare-fun var295_safe_infix_expression_____safe_prev_owned_size___t0 () Bool)
(assert
  (= var295_safe_infix_expression_____safe_prev_owned_size___t0 (theory21_safe var294_infix_expression__t0) )
)

(declare-fun var292_prev_owned_size__t1 () (_ BitVec 64))
(assert
  (= var295_safe_infix_expression_____safe_prev_owned_size___t0 (theory21_safe var292_prev_owned_size__t1) )
)

(declare-fun var296_nullterm_infix_expression_____nullterm_prev_owned_size___t0 () Bool)
(assert
  (= var296_nullterm_infix_expression_____nullterm_prev_owned_size___t0 (theory22_nullterm var294_infix_expression__t0) )
)

(assert
  (= var296_nullterm_infix_expression_____nullterm_prev_owned_size___t0 (theory22_nullterm var292_prev_owned_size__t1) )
)

; type_params_into_ssa prev_owned_size
(declare-fun var292_prev_owned_size__t0 () (_ BitVec 64))
(assert
  (= var292_prev_owned_size__t1  (ite true var294_infix_expression__t0 var292_prev_owned_size__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:97
; type_params_into_ssa nuowned
; : /home/aep/proj/zz/modules/vec/src/lib.zz:97
; : /home/aep/proj/zz/modules/vec/src/lib.zz:97
(declare-fun var298_unsafe_expression__t0 () (_ BitVec 64))
(declare-fun var299_safe_unsafe_expression_____safe_nuowned___t0 () Bool)
(assert
  (= var299_safe_unsafe_expression_____safe_nuowned___t0 (theory21_safe var298_unsafe_expression__t0) )
)

(declare-fun var297_nuowned__t1 () (_ BitVec 64))
(assert
  (= var299_safe_unsafe_expression_____safe_nuowned___t0 (theory21_safe var297_nuowned__t1) )
)

(declare-fun var300_nullterm_unsafe_expression_____nullterm_nuowned___t0 () Bool)
(assert
  (= var300_nullterm_unsafe_expression_____nullterm_nuowned___t0 (theory22_nullterm var298_unsafe_expression__t0) )
)

(assert
  (= var300_nullterm_unsafe_expression_____nullterm_nuowned___t0 (theory22_nullterm var297_nuowned__t1) )
)

; type_params_into_ssa nuowned
(declare-fun var297_nuowned__t0 () (_ BitVec 64))
(assert
  (= var297_nuowned__t1  (ite true var298_unsafe_expression__t0 var297_nuowned__t0)  )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:98
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:98
; call of safe
; : /home/aep/proj/zz/modules/vec/src/lib.zz:98
; : /home/aep/proj/zz/modules/vec/src/lib.zz:98
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:98
(declare-fun var301_safe_prev_owned___t0 () Bool)
(assert
  (= var301_safe_prev_owned___t0 (theory21_safe var288_prev_owned__t1) )
)

(assert (! var301_safe_prev_owned___t0 :named A13))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:98
(declare-fun var302_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var302_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:99
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:99
; call of safe
; : /home/aep/proj/zz/modules/vec/src/lib.zz:99
; : /home/aep/proj/zz/modules/vec/src/lib.zz:99
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:99
(declare-fun var303_safe_nuowned___t0 () Bool)
(assert
  (= var303_safe_nuowned___t0 (theory21_safe var297_nuowned__t1) )
)

(assert (! var303_safe_nuowned___t0 :named A14))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:99
(declare-fun var304_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var304_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
(declare-fun var305_len_prev_owned___t0 () (_ BitVec 64))
(assert
  (= var305_len_prev_owned___t0 (theory20_len var288_prev_owned__t1) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
(declare-fun var306_infix_expression__t0 () Bool)
(assert
  (=  var306_infix_expression__t0 (bvugt var305_len_prev_owned___t0 var292_prev_owned_size__t1))
)

(assert (! var306_infix_expression__t0 :named A15))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:100
(declare-fun var307_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var307_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
; call of static_attest
; static_attest
; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
; call of len
; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
(declare-fun var308_len_nuowned___t0 () (_ BitVec 64))
(assert
  (= var308_len_nuowned___t0 (theory20_len var297_nuowned__t1) )
)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
(declare-fun var309_infix_expression__t0 () Bool)
(assert
  (=  var309_infix_expression__t0 (bvugt var308_len_nuowned___t0 var292_prev_owned_size__t1))
)

(assert (! var309_infix_expression__t0 :named A16))(check-sat)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:101
(declare-fun var310_literal_Unsigned_1___t0 () (_ BitVec 64))
(assert
  (= var310_literal_Unsigned_1___t0 (_ bv1 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:103
; call of ::log::info
; : /home/aep/proj/zz/modules/vec/src/lib.zz:103
; : /home/aep/proj/zz/modules/vec/src/lib.zz:103
(declare-fun var311_literal_string__prev_owned_size__d___t0 () (_ BitVec 64))
(declare-fun var312_true__t0 () Bool)
(assert
  (= var312_true__t0 (theory21_safe var311_literal_string__prev_owned_size__d___t0) )
)

(assert
  var312_true__t0
)

(declare-fun var313_true__t0 () Bool)
(assert
  (= var313_true__t0 (theory22_nullterm var311_literal_string__prev_owned_size__d___t0) )
)

(assert
  var313_true__t0
)

(declare-fun var314_len_literal_string__prev_owned_size__d____t0 () (_ BitVec 64))
(assert
  (= var314_len_literal_string__prev_owned_size__d____t0 (theory20_len var311_literal_string__prev_owned_size__d___t0) )
)

(assert
  (= var314_len_literal_string__prev_owned_size__d____t0 (_ bv19 64))

)

; : /home/aep/proj/zz/modules/log/src/lib.zz:68
(declare-fun var315_literal_string__vec___t0 () (_ BitVec 64))
(declare-fun var316_true__t0 () Bool)
(assert
  (= var316_true__t0 (theory21_safe var315_literal_string__vec___t0) )
)

(assert
  var316_true__t0
)

(declare-fun var317_true__t0 () Bool)
(assert
  (= var317_true__t0 (theory22_nullterm var315_literal_string__vec___t0) )
)

(assert
  var317_true__t0
)

(declare-fun var318_len_literal_string__vec____t0 () (_ BitVec 64))
(assert
  (= var318_len_literal_string__vec____t0 (theory20_len var315_literal_string__vec___t0) )
)

(assert
  (= var318_len_literal_string__vec____t0 (_ bv4 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:103
(declare-fun var319_literal_string__prev_owned_size__d___t0 () (_ BitVec 64))
(declare-fun var320_true__t0 () Bool)
(assert
  (= var320_true__t0 (theory21_safe var319_literal_string__prev_owned_size__d___t0) )
)

(assert
  var320_true__t0
)

(declare-fun var321_true__t0 () Bool)
(assert
  (= var321_true__t0 (theory22_nullterm var319_literal_string__prev_owned_size__d___t0) )
)

(assert
  var321_true__t0
)

(declare-fun var322_len_literal_string__prev_owned_size__d____t0 () (_ BitVec 64))
(assert
  (= var322_len_literal_string__prev_owned_size__d____t0 (theory20_len var319_literal_string__prev_owned_size__d___t0) )
)

(assert
  (= var322_len_literal_string__prev_owned_size__d____t0 (_ bv19 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:103
;callsite_assert
(push 1)

; : /home/aep/proj/zz/modules/log/src/lib.zz:68
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var323_safe_literal_string__prev_owned_size__d____t0 () Bool)
(assert
  (= var323_safe_literal_string__prev_owned_size__d____t0 (theory21_safe var319_literal_string__prev_owned_size__d___t0) )
)

; : /home/aep/proj/zz/modules/log/src/lib.zz:68
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var324_safe_literal_string__vec____t0 () Bool)
(assert
  (= var324_safe_literal_string__vec____t0 (theory21_safe var315_literal_string__vec___t0) )
)

(push 1)

(assert
  (and true (or (not var323_safe_literal_string__prev_owned_size__d____t0 ) (not var324_safe_literal_string__vec____t0 ) ))

)

(check-sat)

; unsat / pass
(pop 1)

;end of callsite_assert
(pop 1)

(declare-fun var323_safe_literal_string__prev_owned_size__d____t0 () Bool)
(declare-fun var324_safe_literal_string__vec____t0 () Bool)
; borrows after call
; end of borrows after call
; : /home/aep/proj/zz/modules/vec/src/lib.zz:103
; callsite effects
; end of callsite effects
; : /home/aep/proj/zz/modules/vec/src/lib.zz:104
; call of ::log::info
; : /home/aep/proj/zz/modules/vec/src/lib.zz:104
; : /home/aep/proj/zz/modules/vec/src/lib.zz:104
(declare-fun var326_literal_string__nusize__d___t0 () (_ BitVec 64))
(declare-fun var327_true__t0 () Bool)
(assert
  (= var327_true__t0 (theory21_safe var326_literal_string__nusize__d___t0) )
)

(assert
  var327_true__t0
)

(declare-fun var328_true__t0 () Bool)
(assert
  (= var328_true__t0 (theory22_nullterm var326_literal_string__nusize__d___t0) )
)

(assert
  var328_true__t0
)

(declare-fun var329_len_literal_string__nusize__d____t0 () (_ BitVec 64))
(assert
  (= var329_len_literal_string__nusize__d____t0 (theory20_len var326_literal_string__nusize__d___t0) )
)

(assert
  (= var329_len_literal_string__nusize__d____t0 (_ bv10 64))

)

; : /home/aep/proj/zz/modules/log/src/lib.zz:68
(declare-fun var330_literal_string__vec___t0 () (_ BitVec 64))
(declare-fun var331_true__t0 () Bool)
(assert
  (= var331_true__t0 (theory21_safe var330_literal_string__vec___t0) )
)

(assert
  var331_true__t0
)

(declare-fun var332_true__t0 () Bool)
(assert
  (= var332_true__t0 (theory22_nullterm var330_literal_string__vec___t0) )
)

(assert
  var332_true__t0
)

(declare-fun var333_len_literal_string__vec____t0 () (_ BitVec 64))
(assert
  (= var333_len_literal_string__vec____t0 (theory20_len var330_literal_string__vec___t0) )
)

(assert
  (= var333_len_literal_string__vec____t0 (_ bv4 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:104
(declare-fun var334_literal_string__nusize__d___t0 () (_ BitVec 64))
(declare-fun var335_true__t0 () Bool)
(assert
  (= var335_true__t0 (theory21_safe var334_literal_string__nusize__d___t0) )
)

(assert
  var335_true__t0
)

(declare-fun var336_true__t0 () Bool)
(assert
  (= var336_true__t0 (theory22_nullterm var334_literal_string__nusize__d___t0) )
)

(assert
  var336_true__t0
)

(declare-fun var337_len_literal_string__nusize__d____t0 () (_ BitVec 64))
(assert
  (= var337_len_literal_string__nusize__d____t0 (theory20_len var334_literal_string__nusize__d___t0) )
)

(assert
  (= var337_len_literal_string__nusize__d____t0 (_ bv10 64))

)

; : /home/aep/proj/zz/modules/vec/src/lib.zz:104
;callsite_assert
(push 1)

; : /home/aep/proj/zz/modules/log/src/lib.zz:68
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var338_safe_literal_string__nusize__d____t0 () Bool)
(assert
  (= var338_safe_literal_string__nusize__d____t0 (theory21_safe var334_literal_string__nusize__d___t0) )
)

; : /home/aep/proj/zz/modules/log/src/lib.zz:68
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var339_safe_literal_string__vec____t0 () Bool)
(assert
  (= var339_safe_literal_string__vec____t0 (theory21_safe var330_literal_string__vec___t0) )
)

(push 1)

(assert
  (and true (or (not var338_safe_literal_string__nusize__d____t0 ) (not var339_safe_literal_string__vec____t0 ) ))

)

(check-sat)

; unsat / pass
(pop 1)

;end of callsite_assert
(pop 1)

(declare-fun var338_safe_literal_string__nusize__d____t0 () Bool)
(declare-fun var339_safe_literal_string__vec____t0 () Bool)
; borrows after call
; end of borrows after call
; : /home/aep/proj/zz/modules/vec/src/lib.zz:104
; callsite effects
; end of callsite effects
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
; call of ::mem::copy
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
; : /home/aep/proj/zz/modules/vec/src/lib.zz:106
;callsite_assert
(push 1)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:3
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var341_safe_nuowned___t0 () Bool)
(assert
  (= var341_safe_nuowned___t0 (theory21_safe var297_nuowned__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:3
; call of safe
; collecting theory invocation arguments
; end of collecting theory invocation arguments
(declare-fun var342_safe_prev_owned___t0 () Bool)
(assert
  (= var342_safe_prev_owned___t0 (theory21_safe var288_prev_owned__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; call of len
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
(declare-fun var343_len_nuowned___t0 () (_ BitVec 64))
(assert
  (= var343_len_nuowned___t0 (theory20_len var297_nuowned__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
; : /home/aep/proj/zz/modules/mem/src/lib.zz:4
(declare-fun var344_infix_expression__t0 () Bool)
(assert
  (=  var344_infix_expression__t0 (bvuge var343_len_nuowned___t0 var292_prev_owned_size__t1))
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; call of len
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; collecting theory invocation arguments
; end of collecting theory invocation arguments
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
(declare-fun var345_len_prev_owned___t0 () (_ BitVec 64))
(assert
  (= var345_len_prev_owned___t0 (theory20_len var288_prev_owned__t1) )
)

; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
; : /home/aep/proj/zz/modules/mem/src/lib.zz:5
(declare-fun var346_infix_expression__t0 () Bool)
(assert
  (=  var346_infix_expression__t0 (bvuge var345_len_prev_owned___t0 var292_prev_owned_size__t1))
)

(push 1)

(assert
  (and true (or (not var341_safe_nuowned___t0 ) (not var342_safe_prev_owned___t0 ) (not var344_infix_expression__t0 ) (not var346_infix_expression__t0 ) ))

)

(check-sat)

