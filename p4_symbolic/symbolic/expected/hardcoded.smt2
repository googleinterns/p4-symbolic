; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let ((?x71 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x72 (= standard_metadata.ingress_port ?x71)))
 (let (($x74 (ite $x72 false true)))
 (and (and (not (or false false)) $x74) (= (- 1) (- 1)))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let ((?x71 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x72 (= standard_metadata.ingress_port ?x71)))
 (let (($x75 (ite $x72 true false)))
 (and (and (not (or false false)) $x75) (= (- 1) (- 1)))))))
(check-sat)

