Introduction
============

Yices is an SMT solver developed in 
`SRI International <http://www.sri.com/>`_'s 
`Computer Science Laboratory <http://www.sri.com/about/organization/information-computing-sciences/computer-science-laboratory>`_.

Yices decides the satisfiability of formulas containing uninterpreted
function symbols, linear real and integer arithmetic, scalar types,
tuples, arrays, and bitvectors. One can interact with Yices using
scripts in the Yices input language, or using the 
`SMT-LIB <http://www.smtlib.org/>`_ notation. Yices can also be used as a
library via its C-API.



Here is a simple example script in the Yices language::

  (define-type BV (bitvector 32))

  (define a::BV)
  (define b::BV)
  (define c::BV (mk-bv 32 1008832))
  (define d::BV)

  (assert (= a (bv-or (bv-and (mk-bv 32 255) (bv-not (bv-or b (bv-not c)))) 
                      (bv-and c (bv-xor d (mk-bv 32 1023))))))

  (check)

  (show-model)
  (eval a)
  (eval b)
  (eval c)
  (eval d)

This script defines a type called ``BV`` that denotes bitvectors of
32bits; it then declares four constants ``a``, ``b``, ``c``, and ``d``
of that type and assert a constraint on these four constants. The
command ``(check)`` checks whether the constatin is satisfiable. Since
it is, command ``(show-model)`` displays the satisfying model. Then
the ``(eval ...)`` command shows the value of different terms in this
model. Functions such as ``bv-or`` and ``bv-and`` denote built-in
Yices functions that operate on bitvectors.

