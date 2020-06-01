;; Packet attributes
(declare-const ingress_port Int)
(declare-const dstAddr (_ BitVec 32))

;; Table output parameters
(declare-const vrf Int)

;; Final output attributes
(declare-const egress_spec Int)

;; Table Matches
;; port_to_vrf
(define-fun port_to_vrf0 () Bool (= ingress_port 0))
(define-fun port_to_vrf1 () Bool (= ingress_port 1))

;; vrf_ip_to_port
;;
;; There are several ways to handle lpm overlaps, priorities, etc
;; one simple way is to define each key match as its own alias indpendently
;; then combine them when defining a row match with the appropriate negations.
;;
;; It would have been nice to always mindlessly negate all other lpm matches when defining
;; one match. However, this won't work:
;; (1) there are other field matches  (e.g. vrf) and if they are different, there is no overlap.
;; (2) lpm overlaps are directional, they must be included in the largest prefix, but not the others.
;;
(define-fun vrf_ip_to_port0_lpm () Bool (= ((_ extract 31 8) dstAddr) #x0a0a00)) ;; 10.10.0.*
(define-fun vrf_ip_to_port1_lpm () Bool (= ((_ extract 31 16) dstAddr) #x0a0a)) ;; 10.10.*.*
(define-fun vrf_ip_to_port2_lpm () Bool (= ((_ extract 31 16) dstAddr) #x1414)) ;; 20.20.*.*

(define-fun vrf_ip_to_port0 () Bool (and
    vrf_ip_to_port0_lpm
    (= vrf 10)
))
(define-fun vrf_ip_to_port1 () Bool (and
    ;; our code determines which combinations are needed
    ;; can invoke the SMT solver to find when!
    (and (not vrf_ip_to_port0_lpm) vrf_ip_to_port1_lpm)
    (= vrf 10)
))
(define-fun vrf_ip_to_port2 () Bool (and
    vrf_ip_to_port2_lpm
    (= vrf 20)
))

;; Branches
(define-fun set_port_if1_then () Bool (= dstAddr #x0a0a0000))
(define-fun set_port_if1_else () Bool (not (= dstAddr #x0a0a0000)))

;; link vrf value to table match
;;
;; simple way of doing it
;; encode the table mechanism in SMT
;; if statements proportional to table size
;; not very efficient probably
;;
(assert (= vrf
    (ite port_to_vrf0 10
        (ite port_to_vrf1 20
            -1
        )
    )
))

;; Similarly, link output actions to the rest of the follow
(assert (= egress_spec
    (ite set_port_if1_then 0
        (ite vrf_ip_to_port0 1
            (ite vrf_ip_to_port1 2
                (ite vrf_ip_to_port2 3
                    -1
                )
            )
        )
    )
))

;; Validity: that a packet is not dropped
(define-fun not_dropped () Bool (not (= egress_spec -1)))

;; Combinations
;;
;; Mindlessly dump all combintations, even ones that are obviously impossible.
;;
(push)
(echo "combination 1")
(assert (and port_to_vrf0 vrf_ip_to_port0 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 2")
(assert (and port_to_vrf0 vrf_ip_to_port0 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 3")
(assert (and port_to_vrf0 vrf_ip_to_port1 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 4")
(assert (and port_to_vrf0 vrf_ip_to_port1 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 5")
(assert (and port_to_vrf0 vrf_ip_to_port2 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 6")
(assert (and port_to_vrf0 vrf_ip_to_port2 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 7")
(assert (and port_to_vrf1 vrf_ip_to_port0 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 8")
(assert (and port_to_vrf1 vrf_ip_to_port0 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 9")
(assert (and port_to_vrf1 vrf_ip_to_port1 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 10")
(assert (and port_to_vrf1 vrf_ip_to_port1 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 11")
(assert (and port_to_vrf1 vrf_ip_to_port2 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 12")
(assert (and port_to_vrf1 vrf_ip_to_port2 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

;; Alternatively, you can have partial queries
;; For example:
;; Give me any valid packet
;;
(push)
(echo "Any valid packet")
(assert not_dropped)
(check-sat)
(get-model)
(echo "")
(pop)

;; Give me a packet that will have output port 3
(push)
(echo "output = 3")
(assert (= egress_spec 3))
(check-sat)
(get-model)
(echo "")
(pop)


;; Give me a packet with output port 2 and vrf 10
(push)
(echo "output = 2 and vrf = 10")
(assert (and (= egress_spec 2) (= vrf 10)))
(check-sat)
(get-model)
(echo "")
(pop)

;; Partial Trace plus output port is 1
(push)
(echo "output = 1 and port to vrf entry 0 is hit")
(assert (and (= egress_spec 1) port_to_vrf0))
(check-sat)
(get-model)
(echo "")
(pop)
