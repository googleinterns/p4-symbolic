; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let ((?x70 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x71 (= standard_metadata.ingress_port ?x70)))
 (let (($x74 (ite $x71 true false)))
 (and (and (not false) $x74) (= (- 1) (- 1)))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let ((?x70 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x71 (= standard_metadata.ingress_port ?x70)))
 (let (($x73 (ite $x71 false true)))
 (and (and (not false) $x73) (= (- 1) (- 1)))))))
(check-sat)

