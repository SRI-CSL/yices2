(set-logic UF)
(set-info :source | Simple list theorem |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort List 0)
(declare-sort Elem 0)

(declare-fun cons (Elem List) List)
(declare-fun nil () List)
(declare-fun car (List) Elem)
(declare-fun cdr (List) List)

(assert (forall ((x Elem) (y List)) (= (car (cons x y)) x)))
(assert (forall ((x Elem) (y List)) (= (cdr (cons x y)) y)))
(assert (exists ((x1 Elem) (y1 List) (x2 Elem) (y2 List)) (and (= (cons x1 y1) (cons x2 y2)) (or (not (= x1 x2)) (not (= y1 y2))))))
(check-sat)
