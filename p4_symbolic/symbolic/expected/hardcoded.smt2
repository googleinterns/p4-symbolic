; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x64 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x64)))
(assert
 (let ((?x44 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x45 (= standard_metadata.ingress_port ?x44)))
 (let (($x47 (and true $x45)))
 (let (($x48 (and true (not $x45))))
 (let ((?x53 (ite $x48 ?x44 (ite $x47 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (or (or (= ?x53 (_ bv455 9)) (= ?x53 (_ bv0 9))) (= ?x53 (_ bv1 9)))))))))
(assert
 (let ((?x44 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x45 (= standard_metadata.ingress_port ?x44)))
 (let (($x47 (and true $x45)))
 (let (($x54 (ite $x45 $x47 false)))
 (let (($x48 (and true (not $x45))))
 (let ((?x53 (ite $x48 ?x44 (ite $x47 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x57 (= ?x53 (_ bv455 9))))
 (and (and (not $x57) $x54) (= (- 1) (- 1)))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun standard_metadata.egress_spec () (_ BitVec 9))
(assert
 (let (($x64 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x64)))
(assert
 (let ((?x44 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x45 (= standard_metadata.ingress_port ?x44)))
 (let (($x47 (and true $x45)))
 (let (($x48 (and true (not $x45))))
 (let ((?x53 (ite $x48 ?x44 (ite $x47 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (or (or (= ?x53 (_ bv455 9)) (= ?x53 (_ bv0 9))) (= ?x53 (_ bv1 9)))))))))
(assert
 (let (($x48 (and true (not (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x44 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x45 (= standard_metadata.ingress_port ?x44)))
 (let (($x55 (ite $x45 false $x48)))
 (let (($x47 (and true $x45)))
 (let ((?x53 (ite $x48 ?x44 (ite $x47 (concat (_ bv0 8) (_ bv1 1)) standard_metadata.egress_spec))))
 (let (($x57 (= ?x53 (_ bv455 9))))
 (and (and (not $x57) $x55) (= (- 1) (- 1)))))))))))
(check-sat)

