(set-logic UF)

(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)

(assert (not y))
(assert (not z))
(assert
  (not
    (xor
      (and (forall ((b Bool)) b) x)
      z
      y
      true
    )
  )
)

(check-sat)
