(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :author |Thomas Sturm, CNRS France, http://science.thomas-sturm.de|)
(set-info :source |
Transmitted by: Thomas Sturm
Generated on: 20161105
Received on: 20161105
Generator: RedLog, http://www.redlog.eu/
Application: qualitative analysis of systems of ODE in physics, chemistry, and the life sciences
Publication: Algebraic Biology 2008, doi:10.1007/978-3-540-85101-1_15
Additional information:
All problems have the following form: a certain polynomial has a zero where all variables are positive.  Interval solutions for satisfiable problems is a valuable information.
|)
(set-info :series |MBO - Methylene Blue Oscillator System|)
(set-info :instance |E22E23|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= (+ (* (* 
h1 h1) h3 j2) (* (* h1 h1) h5 j2) (* (* h1 h1) h5) (* (* h1 h1) h6 j2) (* (* h1 
h1) h6) (* h1 (* h3 h3) (* j2 j2)) (* h1 (* h3 h3) j2) (* 2 h1 h3 h4 j2) (* h1 
h3 h4) (* 2 h1 h3 h5 (* j2 j2)) (* 4 h1 h3 h5 j2) (* 2 h1 h3 h5) (* 2 h1 h3 h6 
(* j2 j2)) (* 5 h1 h3 h6 j2) (* 2 h1 h3 h6) (* 2 h1 h4 h5 j2) (* 2 h1 h4 h5) (* 
2 h1 h4 h6 j2) (* h1 h4 h6) (* h1 (* h5 h5) (* j2 j2)) (* 2 h1 (* h5 h5) j2) (* 
h1 (* h5 h5)) (* 2 h1 h5 h6 (* j2 j2)) (* 4 h1 h5 h6 j2) (* 2 h1 h5 h6) (* h1 
(* h6 h6) (* j2 j2)) (* 2 h1 (* h6 h6) j2) (* h1 (* h6 h6)) (* (* h3 h3) h4 (* 
j2 j2)) (* 2 (* h3 h3) h4 j2) (* (* h3 h3) h4) (* (* h3 h3) h5 (* j2 j2 j2)) (* 
3 (* h3 h3) h5 (* j2 j2)) (* 3 (* h3 h3) h5 j2) (* (* h3 h3) h5) (* 2 (* h3 h3) 
h6 (* j2 j2)) (* 3 (* h3 h3) h6 j2) (* (* h3 h3) h6) (* h3 (* h4 h4) j2) (* h3 
(* h4 h4)) (* 2 h3 h4 h5 (* j2 j2)) (* 4 h3 h4 h5 j2) (* 2 h3 h4 h5) (* 2 h3 h4 
h6 (* j2 j2)) (* 5 h3 h4 h6 j2) (* 2 h3 h4 h6) (* h3 (* h5 h5) (* j2 j2 j2)) (* 
3 h3 (* h5 h5) (* j2 j2)) (* 3 h3 (* h5 h5) j2) (* h3 (* h5 h5)) (* 2 h3 h5 h6 
(* j2 j2 j2)) (* 6 h3 h5 h6 (* j2 j2)) (* 6 h3 h5 h6 j2) (* 2 h3 h5 h6) (* 2 h3 
(* h6 h6) (* j2 j2)) (* 3 h3 (* h6 h6) j2) (* h3 (* h6 h6)) (* (* h4 h4) h5 j2) 
(* (* h4 h4) h5) (* (* h4 h4) h6 j2) (* h4 (* h5 h5) (* j2 j2)) (* 2 h4 (* h5 h5
) j2) (* h4 (* h5 h5)) (* 2 h4 h5 h6 (* j2 j2)) (* 4 h4 h5 h6 j2) (* 2 h4 h5 h6)
 (* h4 (* h6 h6) (* j2 j2)) (* h4 (* h6 h6) j2) (* (* h5 h5) h6 (* j2 j2 j2)) 
(* 3 (* h5 h5) h6 (* j2 j2)) (* 3 (* h5 h5) h6 j2) (* (* h5 h5) h6) (* h5 (* h6 
h6) (* j2 j2 j2)) (* 3 h5 (* h6 h6) (* j2 j2)) (* 3 h5 (* h6 h6) j2) (* h5 (* h6
 h6))) 0)))
(check-sat)
(exit)
