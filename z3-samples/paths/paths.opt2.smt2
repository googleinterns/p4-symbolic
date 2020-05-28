;; Packet attributes
(declare-const ingress_port Int)
(declare-const dstAddr (_ BitVec 32))

;; Table output parameters
(declare-const vrf Int)

;; Table Matches
;; port_to_vrf
(define-fun port_to_vrf0 () Bool (= ingress_port 0))
(define-fun port_to_vrf1 () Bool (= ingress_port 1))

;; vrf_ip_to_port
(define-fun vrf_ip_to_port0_lpm () Bool (= ((_ extract 31 8) dstAddr) #x0a0a00)) ;; 10.10.0.*
(define-fun vrf_ip_to_port1_lpm () Bool (= ((_ extract 31 16) dstAddr) #x0a0a)) ;; 10.10.*.*
(define-fun vrf_ip_to_port2_lpm () Bool (= ((_ extract 31 16) dstAddr) #x1414)) ;; 20.20.*.*

(define-fun vrf_ip_to_port0 () Bool (and
    vrf_ip_to_port0_lpm
    (= vrf 10)
))
(define-fun vrf_ip_to_port1 () Bool (and
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
;; Better way:
;; define all the different values for each row using a reasonable naming convention
;; our code knows to use value<i> exactly for combinations with match<i>
(define-fun vrf0 () Bool (= vrf 10))
(define-fun vrf1 () Bool (= vrf 20))

;; Combinations
;;
;; Our code can ignore combinations that are obviously unsat
;; for example, table matches that are contradictory
;; if statements are probably harder.
;;
;; Another idea is to invoke the solver incremently
;; if a prefix of a combination is unsat, all additions to it are also unsat
;; and can be ignored.
;;
(push)
(echo "combination 1")
(assert (and port_to_vrf0 vrf0 vrf_ip_to_port0 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 2")
(assert (and port_to_vrf0 vrf0 vrf_ip_to_port0 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 3")
(assert (and port_to_vrf0 vrf0 vrf_ip_to_port1 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 4")
(assert (and port_to_vrf0 vrf0 vrf_ip_to_port1 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 5")
(assert (and port_to_vrf1 vrf1 vrf_ip_to_port2 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 6")
(assert (and port_to_vrf1 vrf1 vrf_ip_to_port2 set_port_if1_else))
(check-sat)
(get-model)
(echo "")
(pop)

