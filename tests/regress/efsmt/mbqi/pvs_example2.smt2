(set-logic UF)

(declare-sort |U_beings| 0)
(declare-sort |worlds[U_beings]| 0)
(declare-sort |pvsInt| 0)

(declare-const w!1 |worlds[U_beings]|)
(declare-const x!1 |U_beings|)
(declare-const v!1 |worlds[U_beings]|)
(declare-const z!1 |pvsInt|)

(declare-fun vind (|worlds[U_beings]| |U_beings|) Bool)
(declare-fun access (|worlds[U_beings]| |worlds[U_beings]|) Bool)
(declare-fun re? (|U_beings| |worlds[U_beings]|) Bool)
(declare-fun g (|U_beings| |worlds[U_beings]|) |pvsInt|)
(declare-fun gt (|pvsInt| |pvsInt|) Bool)


;{-1}  vind(w!1)(x!1)
(define-fun constraint-1 () Bool
	(vind w!1 x!1)
)

;{-2}  FORALL (a: U_beings, v, w: worlds[U_beings]):
;        vind(w)(a) AND access(w, v) => vind(v)(a)
(define-fun constraint-2 () Bool
  (forall ((a |U_beings|)) 
	(forall ((v |worlds[U_beings]|) (w |worlds[U_beings]|))
		(=> 
			(and
				(vind w a)
				(access w v)
			)
			(vind v a)
))))

;{-3}  FORALL (w_1: worlds[U_beings]):
;        FORALL (x_1: (vind(w_1))):
;          FORALL (x: (vind(w_1))):
;            (NOT re?(x_1)(w_1) AND
;              (EXISTS (v: worlds[U_beings]): access(w_1, v) AND re?(x)(v)))
;             =>
;             (EXISTS z:
;                z = g(x_1)(w_1) AND
;                 (EXISTS (v: worlds[U_beings]):
;                    access(w_1, v) AND g(x)(v) > z))
(define-fun constraint-3 () Bool
  (forall ((w_1 |worlds[U_beings]|)) 
	(forall ((x_1 |U_beings|) (x |U_beings|))
		(=>
			(and
				(not (re? x_1 w_1))
				(exists ((v |worlds[U_beings]|))
					(and
						(access w_1 v)
						(re? x v)
					)
				)
			)
			(exists ((z |pvsInt|))
				(and
					(= z (g x_1 w_1))
					(exists ((v |worlds[U_beings]|))
						(and
							(access w_1 v)
							(gt (g x v) z)
						)
					)
				)
			)
))))

;{-4}  access(w!1, v!1)
(define-fun constraint-4 () Bool
	(access w!1 v!1)
)

;{-5}  re?(x!1)(v!1)
(define-fun constraint-5 () Bool
	(re? x!1 v!1)
)

;{-6}  z!1 = g(x!1)(w!1)
(define-fun constraint-6 () Bool
	(= z!1 (g x!1 w!1))
)

;{1}   re?(x!1)(w!1)
(define-fun constraint1 () Bool
	(re? x!1 w!1)
)

;{2}   EXISTS (v: worlds[U_beings]):
;        access(w!1, v) AND (EXISTS (x: (vind(v))): g(x)(v) > g(x!1)(w!1))
(define-fun constraint2 () Bool
	(exists ((v |worlds[U_beings]|))
		(and
			(access w!1 v)
			(exists ((x |U_beings|))
				(gt (g x v) (g x!1 w!1))
))))


(assert 
	(not 
		(=>
			(and
				constraint-1
				constraint-2
				constraint-3
				constraint-4
				constraint-5
				constraint-6
			)
			(or
				constraint1
				constraint2
			)
)))


(check-sat)
