(theory Fixed_Size_BitVectors

 :smt-lib-version 2.0
 :written_by "Silvio Ranise, Cesare Tinelli, and Clark Barrett"
 :date "2010-05-02"

 :notes
  "This theory declaration defines a core theory for fixed-size bitvectors 
   where the operations of concatenation and extraction of bitvectors as well 
   as the usual logical and arithmetic operations are overloaded.
  "

 :sorts_description "
    All sort symbols of the form (_ BitVec m)
    where m is a numeral greater than 0.
 "

 :funs_description "
    All binaries #bX of sort (_ BitVec m) where m is the number of digits in X.
    All hexadeximals #xX of sort (_ BitVec m) where m is 4 times the number of
    digits in X.    
 "

 :funs_description "
    All function symbols with declaration of the form

      (concat (_ BitVec i) (_ BitVec j) (_ BitVec m))

    where
    - i,j,m are numerals
    - i,j > 0
    - i + j = m
 "

 :funs_description "
    All function symbols with declaration of the form

      ((_ extract i j) (_ BitVec m) (_ BitVec n))

    where
    - i,j,m,n are numerals
    - m > i >= j >= 0,
    - n = i-j+1
 "

 :funs_description "
    All function symbols with declaration of the form

       (op1 (_ BitVec m) (_ BitVec m))
    or
       (op2 (_ BitVec m) (_ BitVec m) (_ BitVec m))

    where
    - op1 is from {bvnot, bvneg}
    - op2 is from {bvand, bvor, bvadd, bvmul, bvudiv, bvurem, bvshl, bvlshr}
    - m is a numeral greater than 0
 "

 :funs_description "
    All function symbols with declaration of the form

       (bvult (_ BitVec m) (_ BitVec m) Bool)

    where
    - m is a numeral greater than 0
 "

 :definition
  "For every expanded signature Sigma, the instance of Fixed_Size_BitVectors
   with that signature is the theory consisting of all Sigma-models that 
   satisfy the constraints detailed below.

   The sort (_ BitVec m), for m > 0, is the set of finite functions
   whose domain is the initial segment of the naturals [0...m), meaning
   that 0 is included and m is excluded, and the co-domain is {0,1}.

   To define some of the semantics below, we need the following additional
   functions :

   o _ div _,  which takes an integer x >= 0 and an integer y > 0 and returns
     the integer part of x divided by y (i.e., truncated integer division).

   o _ rem _, which takes an integer x >= 0 and y > 0 and returns the
     remainder when x is divided by y.  Note that we always have the following
     equivalence (for y > 0): (x div y) * y + (x rem y) = x.

   o bv2nat, which takes a bitvector b: [0...m) --> {0,1}
     with 0 < m, and returns an integer in the range [0...2^m),
     and is defined as follows:

       bv2nat(b) := b(m-1)*2^{m-1} + b(m-2)*2^{m-2} + ... + b(0)*2^0

   o nat2bv[m], with 0 < m, which takes a non-negative integer
     n and returns the (unique) bitvector b: [0,...,m) -> {0,1}
     such that

       b(m-1)*2^{m-1} + ... + b(0)*2^0 = n rem 2^m

   The semantic interpretation [[_]] of well-sorted BitVec-terms is
   inductively defined as follows.

   - Variables

   If v is a variable of sort (_ BitVec m) with 0 < m, then
   [[v]] is some element of [{0,...,m-1} -> {0,1}], the set of total
   functions from {0,...,m-1} to {0,1}.

   - Constant symbols

   The constant symbols #b0 and #b1 of sort (_ BitVec 1) are defined as follows

   [[#b0]] := \lambda x : [0,1). 0
   [[#b1]] := \lambda x : [0,1). 1

   More generally, given a string #b followed by a sequence of 0's and 1's,
   if n is the numeral represented in base 2 by the sequence of 0's and 1's
   and m is the length of the sequence, then the term represents
   nat2bv[m](n).

   The string #x followed by a sequence of digits and/or letters from A to
   F is interpreted similarly: if n is the numeral represented in hexadecimal
   (base 16) by the sequence of digits and letters from A to F and m is four
   times the length of the sequence, then the term represents nat2bv[m](n).
   For example, #xFF is equivalent to #b11111111.

   - Function symbols for concatenation

   [[(concat s t)]] := \lambda x : [0...n+m).
                          if (x<m) then [[t]](x) else [[s]](x-m)
   where
   s and t are terms of sort (_ BitVec n) and (_ BitVec m), respectively,
   0 < n, 0 < m.

   - Function symbols for extraction

   [[((_ extract i j) s))]] := \lambda x : [0...i-j+1). [[s]](j+x)
   where s is of sort (_ BitVec l), 0 <= j <= i < l.

   - Bit-wise operations

   [[(bvnot s)]] := \lambda x : [0...m). if [[s]](x) = 0 then 1 else 0

   [[(bvand s t)]] := \lambda x : [0...m).
                         if [[s]](x) = 0 then 0 else [[t]](x)

   [[(bvor s t)]] := \lambda x : [0...m).
                         if [[s]](x) = 1 then 1 else [[t]](x)

   where s and t are both of sort (_ BitVec m) and 0 < m.

   - Arithmetic operations

   Now, we can define the following operations.  Suppose s and t are both terms
   of sort (_ BitVec m), m > 0.

   [[(bvneg s)]] := nat2bv[m](2^m - bv2nat([[s]]))

   [[(bvadd s t)]] := nat2bv[m](bv2nat([[s]]) + bv2nat([[t]]))

   [[(bvmul s t)]] := nat2bv[m](bv2nat([[s]]) * bv2nat([[t]]))

   [[(bvudiv s t)]] := if bv2nat([[t]]) != 0 then
                          nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))

   [[(bvurem s t)]] := if bv2nat([[t]]) != 0 then
                          nat2bv[m](bv2nat([[s]]) rem bv2nat([[t]]))

   - Shift operations

   Suppose s and t are both terms of sort (_ BitVec m), m > 0.  We make use of
   the definitions given for the arithmetic operations, above.

   [[(bvshl s t)]] := nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))

   [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))

   Finally, we can define bvult:

   [[bvult s t]] := true iff bv2nat([[s]]) < bv2nat([[t]])
  "

:notes
  "The constraints on the theory models do not specify the meaning of 
   (bvudiv s t) or (bvurem s t) in case bv2nat([[t]]) is 0.  
   Since the semantics of SMT-LIB's underlying logic associates *total* 
   functions to function symbols, this means that we consider as models
   of this theory *any* interpretation conforming to the specifications 
   in the definition field (and defining bvudiv and bvurem arbitrarily 
   when the second argument evaluates to 0).  
   Solvers supporting this theory then cannot make any any assumptions
   about the value of (bvudiv s t) or (bvurem s t) when t evaluates to 0.
  "

)
