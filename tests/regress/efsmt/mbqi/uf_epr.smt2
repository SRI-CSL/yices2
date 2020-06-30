(set-logic UF)

(declare-sort T 0) 

(declare-fun subtype (T T) Bool)

(declare-const obj-type T)
(declare-const root-type T)

(assert (forall ((x T) (y T)) (=> (and (subtype x y)
                                       (subtype y x))
                                       (= x y))))

(assert (forall ((x T)) (subtype x obj-type)))

(assert (subtype obj-type root-type))

(check-sat)
