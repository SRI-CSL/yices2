(set-logic UF)
(declare-sort worlds 0)

(declare-const w!1 worlds)
(declare-const g worlds)
(declare-const v!1 worlds)

(declare-fun access (worlds worlds) Bool)
(declare-fun val (worlds worlds) Bool)

(define-fun constraint-1 () Bool
  (forall ((w worlds)) 
	(exists ((v worlds)) 
		(and 
			(access w v)
			(val g v)
))))

(define-fun constraint-2 () Bool
  (forall ((w worlds)) 
	(forall ((v worlds)) 
		(=> 
			(access w v)
			(=> 
				(val g v)
				(forall ((v_1 worlds))
					(=>
						(access v v_1)
						(val g v_1)
)))))))

(define-fun constraint-3 () Bool
  (forall ((x worlds) (y worlds) (z worlds)) 
	(=>
		(and 
			(access x y)
			(access x z)
		)
		(access y z)
)))

(define-fun constraint-4 () Bool
	(access w!1 v!1)
)

(define-fun constraint1 () Bool
	(val g v!1)
)

(assert 
	(not 
		(=>
			(and
				constraint-1
				constraint-2
				constraint-3
				constraint-4
			)
			constraint1
)))

(check-sat)
