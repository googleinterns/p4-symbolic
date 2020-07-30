; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let ((?x68 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x69 (= standard_metadata.ingress_port ?x68)))
 (let (($x78 (ite $x69 true false)))
 (and (and (not false) $x78) (= (- 1) (- 1)))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let ((?x68 (concat (_ bv0 8) (_ bv0 1))))
 (let (($x69 (= standard_metadata.ingress_port ?x68)))
 (let (($x77 (ite $x69 false true)))
 (and (and (not false) $x77) (= (- 1) (- 1)))))))
(check-sat)

