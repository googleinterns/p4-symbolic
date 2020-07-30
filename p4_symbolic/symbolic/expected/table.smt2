; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let (($x72 (and true (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1)))))))
 (let (($x82 (and (and true (not $x72)) (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x86 (ite $x82 0 (ite $x72 1 (- 1)))))
 (and (and (not false) (or (or true $x72) $x82)) (= ?x86 (- 1)))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let (($x72 (and true (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1)))))))
 (let (($x82 (and (and true (not $x72)) (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x86 (ite $x82 0 (ite $x72 1 (- 1)))))
 (let (($x84 (or (or true $x72) $x82)))
 (let (($x98 (and (not false) $x84)))
 (and $x98 (= ?x86 0))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(assert
 (let (($x46 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x46)))
(assert
 (let (($x72 (and true (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv1 1)))))))
 (let (($x82 (and (and true (not $x72)) (and true (= standard_metadata.ingress_port (concat (_ bv0 8) (_ bv0 1)))))))
 (let ((?x86 (ite $x82 0 (ite $x72 1 (- 1)))))
 (and (and (not false) (or (or true $x72) $x82)) (= ?x86 1))))))
(check-sat)

