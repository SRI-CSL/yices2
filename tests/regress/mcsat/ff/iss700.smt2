; Issue 700: wrong sat. For fields of size 1000 or more, libpoly found the
; roots of a constraint in no fixed order and kept them unsorted in the
; feasible set, so a value that the constraint excludes was picked.
(set-logic QF_FFA)
(define-sort F () (_ FiniteField 1019))
(declare-fun y () F)
(declare-fun u () F)
(declare-fun v () F)
(assert (= (ff.mul v y) (as ff0 F)))
(assert (= u (ff.mul u u v v)))
(assert (not (= u (as ff0 F))))
(assert (not (= (ff.mul y y) (ff.add (ff.mul (ff.mul y u) (ff.mul y u) (ff.mul y u)) (ff.mul (as ff2 F) y u)))))
(check-sat)
