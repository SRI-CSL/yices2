(theory Reals

 :smt-lib-version 2.0
 :written_by "Cesare Tinelli"
 :date "2010-04-17"
 :updated "2012-06-20"

 :history
 "Modified the definition of :value attribute to include abstract values
  for irrational algebraic numbers.
 "
 :sorts ((Real 0))

 :funs ((NUMERAL Real)
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
       )

 :values
 "The set of values for the sort Real consists of
  - an abstract value for each irrational algebraic number
  - all numerals
  - all terms of the form (- n) where n is a numeral other than 0
  - all terms of the form (/ m n) or (/ (- m) n) where
    - m is a numeral other than 0,
    - n is a numeral other than 0 and 1,
    - as integers, m and n have no common factors besides 1.
 "
 :definition
 "For every expanded signature Sigma, the instance of Reals with that
  signature is the theory consisting of all Sigma-models that interpret

  - the sort Real as the set of all real numbers,

  - each numeral as the corresponding real number,

  - each decimal as the corresponding real number,

  - / as a total function that coincides with the real division function
    for all inputs x and y where y is non-zero,

  - the other function symbols of Reals as expected.
 "

 :notes
 "Since in SMT-LIB logic all function symbols are interpreted as total
  functions, terms of the form (/ t 0) *are* meaningful in every
  instance of Reals. However, the declaration imposes no constraints
  on their value. This means in particular that
  - for every instance theory T and
  - for every closed terms t1 and t2 of sort Real,
  there is a model of T that satisfies (= t1 (/ t2 0)).
 "

 :notes
 "The restriction of Reals over the signature having just the symbols
  (0 Real)
  (1 Real)
  (- Real Real)
  (+ Real Real Real)
  (* Real Real Real)
  (<= Real Real Bool)
  (<  Real Real Bool)
  coincides with the theory of real closed fields, axiomatized by
  the formulas below:

   - associativity of +
   (forall ((x Real) (y Real) (z Real))
    (= (+ (+ x y) z) (+ x (+ y z))))

   - commutativity of +
   (forall ((x Real) (y Real))
    (= (* x y) (* y x)))

   - 0 is the right (and by commutativity, left) unit of +
   (forall ((x Real)) (= (+ x 0) x))

   - right (and left) inverse wrt +
   (forall ((x Real)) (= (+ x (- x)) 0))

   - associativity of *
   (forall ((x Real) (y Real) (z Real))
    (= (* (* x y) z) (* x (* y z))))

   - commutativity of *
   (forall ((x Real) (y Real)) (= (* x y) (* y x)))

   - 1 is the right (and by commutativity, left) unit of *
   (forall ((x Real)) (= (* x 1) x))

   - existence of right (and left) inverse wrt *
   (forall ((x Real))
    (or (= x 0) (exists (y Real) (= (* x y) 1))))

   - left distributivity of * over +
   (forall ((x Real) (y Real) (z Real))
    (= (* x (+ y z)) (+ (* x y) (* x z))))

   - right distributivity of * over +
   (forall ((x Real) (y Real) (z Real))
    (= (* (+ x y) z) (+ (* x z) (* y z))))

         - non-triviality
   (distinct 0 1)

         - all positive elements have a square root
   (forall (x Real)
    (exists (y Real) (or (= x (* y y)) (= (- x) (* y y)))))

         - axiom schemas for all n > 0
    (forall (x_1 Real) ... (x_n Real)
      (distinct (+ (* x_1 x_1) (+ ... (* x_n x_n)))
         (- 1)))

         - axiom schemas for all odd n > 0 where
    (^ y n) abbreviates the n-fold product of y with itself
     (forall (x_1 Real) ... (x_n Real)
      (exists (y Real)
      (= 0
         (+ (^ y n) (+ (* x_1 (^ y n-1)) (+  ... (+ (* x_{n-1} y) x_n)))))))

         - reflexivity of <=
         (forall (x Real) (<= x x))

         - antisymmetry of <=
         (forall (x Real) (y Real)
   (implies (and (<= x y) (<= y x))
            (= x y)))

         - transitivity of <=
         (forall (x Real) (y Real) (z Real)
   (implies (and (<= x y) (<= y z))
            (<= x z)))

         - totality of <=
         (forall (x Real) (y Real)
   (or (<= x y) (<= y x)))

         - monotonicity of <= wrt +
         (forall (x Real) (y Real) (z Real)
   (implies (<= x y) (<= (+ x z) (+ y z))))

         - monotonicity of <= wrt *
         (forall (x Real) (y Real) (z Real)
   (implies (and (<= x y) (<= 0 z))
            (<= (* z x) (* z y))))

         - definition of <
         (forall (x Real) (y Real)
   (iff (< x y)
        (and (<= x y) (distinct x y)))
         )

  References:
  1) W. Hodges. Model theory. Cambridge University Press, 1993.
  2) PlanetMath, http://planetmath.org/encyclopedia/RealClosedFields.html
 "
)
