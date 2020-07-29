; 
(set-info :status unknown)
(declare-fun standard_metadata.ingress_port () (_ BitVec 9))
(declare-fun ipv4.dstAddr () (_ BitVec 32))
(declare-fun ipv4.$valid$ () Bool)
(assert
 (let (($x63 (= standard_metadata.ingress_port (_ bv1 9))))
 (or (or false (= standard_metadata.ingress_port (_ bv0 9))) $x63)))
(assert
 (let (($x89 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x109 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let ((?x129 (ite ipv4.$valid$ (ite $x109 0 (ite $x89 1 (- 1))) (- 1))))
 (let (($x128 (ite ipv4.$valid$ (or (or true $x89) $x109) false)))
 (let (($x127 (ite ipv4.$valid$ (or false (ite $x109 false (ite $x89 false true))) false)))
 (and (and (not $x127) $x128) (= ?x129 (- 1)))))))))
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
 (let (($x89 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x109 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let ((?x129 (ite ipv4.$valid$ (ite $x109 0 (ite $x89 1 (- 1))) (- 1))))
 (let (($x128 (ite ipv4.$valid$ (or (or true $x89) $x109) false)))
 (let (($x127 (ite ipv4.$valid$ (or false (ite $x109 false (ite $x89 false true))) false)))
 (let (($x141 (and (not $x127) $x128)))
 (and $x141 (= ?x129 0)))))))))
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
 (let (($x89 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv336855040 32))))))
 (let (($x109 (and true (= ((_ extract 31 16) ipv4.dstAddr) ((_ extract 31 16) (_ bv168427520 32))))))
 (let ((?x129 (ite ipv4.$valid$ (ite $x109 0 (ite $x89 1 (- 1))) (- 1))))
 (let (($x128 (ite ipv4.$valid$ (or (or true $x89) $x109) false)))
 (let (($x127 (ite ipv4.$valid$ (or false (ite $x109 false (ite $x89 false true))) false)))
 (and (and (not $x127) $x128) (= ?x129 1))))))))
(check-sat)

