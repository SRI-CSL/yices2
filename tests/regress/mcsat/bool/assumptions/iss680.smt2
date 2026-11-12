; While an MCSAT context has the status sat from an MCSAT check with assumptions,
; the `get-model` command of `yices_smt2` shall print a model that gives true to
; each assertion and to each assumption.
(set-option :produce-models true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (xor a b))
(push 1)
(check-sat-assuming (a c))
(check-sat-assuming (a c))
(get-model)
(pop 1)
(assert (not a))
(check-sat)
(get-value (a b))
