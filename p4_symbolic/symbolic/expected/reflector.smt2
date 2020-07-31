; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x52 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x52)))
(assert
 (let ((?x43 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (or (or (= ?x43 (_ bv455 9)) (= ?x43 (_ bv0 9))) (= ?x43 (_ bv1 9)))))
(assert
 (let ((?x43 (ite true standard_metadata.ingress_port standard_metadata.egress_spec)))
 (let (($x45 (= ?x43 (_ bv455 9))))
 (and (and (not $x45) true) (= (- 1) (- 1))))))
(check-sat)

