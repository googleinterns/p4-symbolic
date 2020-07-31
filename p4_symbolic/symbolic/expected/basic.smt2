; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ipv4.$valid$ () Bool)
(assert
 (let (($x63 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x63)))
(assert
 (let (($x95 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x85 (and true ipv4.$valid$)))
 (let (($x91 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let (($x96 (and $x85 $x91)))
 (let ((?x132 (ite ipv4.$valid$ (ite $x96 0 (ite (and $x85 $x95) 1 (- 1))) (- 1))))
 (let (($x131 (ite ipv4.$valid$ $x85 false)))
 (let (($x142 (and (not (ite (and $x85 (and (not $x91) (not $x95))) true false)) $x131)))
 (and $x142 (= ?x132 (- 1)))))))))))
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
 (let (($x95 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x85 (and true ipv4.$valid$)))
 (let (($x91 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let (($x96 (and $x85 $x91)))
 (let ((?x132 (ite ipv4.$valid$ (ite $x96 0 (ite (and $x85 $x95) 1 (- 1))) (- 1))))
 (let (($x131 (ite ipv4.$valid$ $x85 false)))
 (let (($x142 (and (not (ite (and $x85 (and (not $x91) (not $x95))) true false)) $x131)))
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
 (let (($x95 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x85 (and true ipv4.$valid$)))
 (let (($x91 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let (($x96 (and $x85 $x91)))
 (let ((?x132 (ite ipv4.$valid$ (ite $x96 0 (ite (and $x85 $x95) 1 (- 1))) (- 1))))
 (let (($x131 (ite ipv4.$valid$ $x85 false)))
 (let (($x144 (and (not (ite (and $x85 (and (not $x91) (not $x95))) true false)) $x131)))
 (and $x144 (= ?x132 1))))))))))
(check-sat)

