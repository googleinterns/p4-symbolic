; 
(set-info :status unknown)
(declare-fun ingress_port () Int)
(assert
 (let (($x29 (= ingress_port 1)))
 (or (or false (= ingress_port 0)) $x29)))
(assert
 (let (($x26 (= ingress_port 0)))
 (let (($x54 (and true $x26)))
 (let ((?x56 (ite $x54 0 (ite (and true (= ingress_port 1)) 1 (- 1)))))
 (let (($x55 (or (or false (and true (= ingress_port 1))) $x54)))
 (and (and (not (or false (not $x55))) $x55) (= ?x56 0)))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun ingress_port () Int)
(assert
 (let (($x29 (= ingress_port 1)))
 (or (or false (= ingress_port 0)) $x29)))
(assert
 (let (($x26 (= ingress_port 0)))
 (let (($x54 (and true $x26)))
 (let ((?x56 (ite $x54 0 (ite (and true (= ingress_port 1)) 1 (- 1)))))
 (let (($x55 (or (or false (and true (= ingress_port 1))) $x54)))
 (and (and (not (or false (not $x55))) $x55) (= ?x56 1)))))))
(check-sat)

