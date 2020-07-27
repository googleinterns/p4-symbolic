; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x44 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x44)))
(assert
 (let (($x69 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x76 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let ((?x79 (ite $x76 0 (ite $x69 1 (- 1)))))
 (let (($x77 (or (or false $x69) $x76)))
 (and (and (not (or false (not $x77))) $x77) (= ?x79 0)))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x44 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x44)))
(assert
 (let (($x69 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1))))))
 (let (($x76 (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let ((?x79 (ite $x76 0 (ite $x69 1 (- 1)))))
 (let (($x77 (or (or false $x69) $x76)))
 (and (and (not (or false (not $x77))) $x77) (= ?x79 1)))))))
(check-sat)

