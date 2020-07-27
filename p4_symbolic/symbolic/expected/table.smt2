; 
(set-info :status unknown)
(declare-fun ingress_port () (_ BitVec 9))
(assert
 (let (($x29 (= ingress_port (_ bv1 9))))
 (or (or false (= ingress_port (_ bv0 9))) $x29)))
(assert
 (let (($x61 (and true (= ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let ((?x64 (ite $x61 0 (ite (and true (= ingress_port (concat (_ bv0 8) (_ bv1 1)))) 1 (- 1)))))
 (let (($x62 (or (or false (and true (= ingress_port (concat (_ bv0 8) (_ bv1 1))))) $x61)))
 (and (and (not (or false (not $x62))) $x62) (= ?x64 0))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun ingress_port () (_ BitVec 9))
(assert
 (let (($x29 (= ingress_port (_ bv1 9))))
 (or (or false (= ingress_port (_ bv0 9))) $x29)))
(assert
 (let (($x61 (and true (= ingress_port (concat (_ bv0 8) (_ bv0 1))))))
 (let ((?x64 (ite $x61 0 (ite (and true (= ingress_port (concat (_ bv0 8) (_ bv1 1)))) 1 (- 1)))))
 (let (($x62 (or (or false (and true (= ingress_port (concat (_ bv0 8) (_ bv1 1))))) $x61)))
 (and (and (not (or false (not $x62))) $x62) (= ?x64 1))))))
(check-sat)

