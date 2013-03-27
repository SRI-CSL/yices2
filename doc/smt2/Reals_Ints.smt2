(theory Reals_Ints

 :smt-lib-version 2.0
 :written_by "Cesare Tinelli"
 :date "2010-04-17"
 
 :sorts ((Int 0) (Real 0))

 :funs ((NUMERAL Int) 
        (- Int Int)                 ; negation
        (- Int Int Int :left-assoc) ; subtraction
        (+ Int Int Int :left-assoc) 
        (* Int Int Int :left-assoc)
        (div Int Int Int :left-assoc)
        (mod Int Int Int)
        (abs Int Int)
        (<= Int Int Bool :chainable)
        (<  Int Int Bool :chainable)
        (>= Int Int Bool :chainable)
        (>  Int Int Bool :chainable)
        (DECIMAL Real) 
        (- Real Real)                  ; negation
        (- Real Real Real :left-assoc) ; subtraction
        (+ Real Real Real :left-assoc) 
        (* Real Real Real :left-assoc)
        (/ Real Real Real :left-assoc)
        (<= Real Real Bool :chainable)
        (<  Real Real Bool :chainable)
        (>= Real Real Bool :chainable)
        (>  Real Real Bool :chainable)
        (to_real Int Real)
        (to_int Real Int)
        (is_int Real Bool)
       )

 :funs_description
 "All ranked function symbols of the form
    ((_ divisible n) Int Bool)
  where n is a positive numeral.
 "

 :values
 "The set of values for the sort Int consists of 
  - all numerals,
  - all terms of the form (- n) where n is a numeral other than 0.

  The set of values for the sort Real consists of 
  - all terms of the form (/ (to_real m) (to_real n)) or 
    (/ (- (to_real m)) (to_real n)) where 
    - m is a numeral,
    - n is a numeral other than 0,
    - as integers, m and n have no common factors besides 1.
 "

 :definition 
 "For every expanded signature Sigma, the instance of RealsInts with that 
  signature is the theory consisting of all Sigma-models that interpret:

  - the sort Int as the set of all integer numbers, 

  - the sort Real as the set of all real numbers, 

  - each numeral as the corresponding natural number,

  - to_real as the standard injection of the integers into the reals,

  - the other function symbols with Int arguments as in the theory 
    declaration Ints,

  - each decimal as the corresponding real number,

  - to_int as the function that maps each real number r to its integer part,
    that is, to the largest integer n that satisfies (<= (to_real n) r) 

  - is_int as the function that maps to true all and only the reals in the
    image of to_real,

  - the other function symbols with Real arguments as in the theory 
    declaration Reals.
 "

 :notes
  "By definition of to_int, (to_int (- 1.3)) is equivalent to (- 2), not
   (- 1).
  "

 :notes
 "For each instance T of Reals_Ints, all models of T satisfy the sentence:

  (forall ((x Real))
    (= (is_int x) (= x (to_real (to_int x))))) 
 "
)
