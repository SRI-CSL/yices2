(set-logic QF_BV)
(declare-fun r1 () (_ BitVec 32))
(declare-fun i () (_ BitVec 32))
(declare-fun j () (_ BitVec 32))
(declare-fun k () (_ BitVec 32))
(assert
 (let (($x84 (= (bvadd (bvadd i j) (bvmul (_ bv4294967295 32) k)) (_ bv0 32))))
 (let (($x175 (= (bvadd k (bvmul (_ bv4294967295 32) j)) r1)))
 (let (($x161 (= (bvadd (bvadd (_ bv1 32) j) (bvmul (_ bv4294967295 32) k)) (_ bv0 32))))

 (let ((?x235 (bvmul (_ bv4 32) r1)))
 (let ((?x62 (bvmul (_ bv4 32) i)))
 (let (($x311 (= ?x235 ?x62)))

 (let (($x259 (and $x161 $x175 $x84)))
 (not (=> $x259 $x311))))))))))
(check-sat)

