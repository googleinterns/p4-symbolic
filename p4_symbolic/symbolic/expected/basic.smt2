; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ipv4.$valid$ () Bool)
(assert
 (let (($x63 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x63)))
(assert
 (let (($x85 (and true ipv4.$valid$)))
 (let (($x93 (and $x85 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32)))))))
 (let (($x110 (and $x85 (not $x93))))
 (let (($x115 (and $x110 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32)))))))
 (let ((?x132 (ite ipv4.$valid$ (ite $x115 0 (ite $x93 1 (- 1))) (- 1))))
 (let (($x131 (ite ipv4.$valid$ (or (or true $x93) $x115) false)))
 (and (and (not (ite (and $x110 (not $x115)) true false)) $x131) (= ?x132 (- 1))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ipv4.$valid$ () Bool)
(assert
 (let (($x63 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x63)))
(assert
 (let (($x85 (and true ipv4.$valid$)))
 (let (($x93 (and $x85 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32)))))))
 (let (($x110 (and $x85 (not $x93))))
 (let (($x115 (and $x110 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32)))))))
 (let ((?x132 (ite ipv4.$valid$ (ite $x115 0 (ite $x93 1 (- 1))) (- 1))))
 (let (($x131 (ite ipv4.$valid$ (or (or true $x93) $x115) false)))
 (let (($x142 (and (not (ite (and $x110 (not $x115)) true false)) $x131)))
 (and $x142 (= ?x132 0))))))))))
(check-sat)

; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ipv4.$valid$ () Bool)
(assert
 (let (($x63 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x63)))
(assert
 (let (($x85 (and true ipv4.$valid$)))
 (let (($x93 (and $x85 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32)))))))
 (let (($x110 (and $x85 (not $x93))))
 (let (($x115 (and $x110 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32)))))))
 (let ((?x132 (ite ipv4.$valid$ (ite $x115 0 (ite $x93 1 (- 1))) (- 1))))
 (let (($x131 (ite ipv4.$valid$ (or (or true $x93) $x115) false)))
 (and (and (not (ite (and $x110 (not $x115)) true false)) $x131) (= ?x132 1)))))))))
(check-sat)

