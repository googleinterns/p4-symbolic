; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let (($x73 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x70 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let (($x74 (and true $x70)))
 (let ((?x87 (ite $x74 0 (ite (and true $x73) 1 (- 1)))))
 (and (and (not false) true) (= ?x87 (- 1))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let (($x73 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x70 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let (($x74 (and true $x70)))
 (let ((?x87 (ite $x74 0 (ite (and true $x73) 1 (- 1)))))
 (let (($x97 (and (not false) true)))
 (and $x97 (= ?x87 0))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let (($x73 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x70 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let (($x74 (and true $x70)))
 (let ((?x87 (ite $x74 0 (ite (and true $x73) 1 (- 1)))))
 (and (and (not false) true) (= ?x87 1)))))))
(check-sat)

