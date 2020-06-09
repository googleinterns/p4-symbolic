;; Copyright 2020 Google LLC
;;
;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at
;;
;;      http://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.

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
(assert (=> port_to_vrf0 (= vrf 10)))
(assert (=> port_to_vrf1 (= vrf 20)))
(assert (=> (and (not port_to_vrf0) (not port_to_vrf1)) (= vrf -1)))

;; link output values to their paths/traces
(assert (=> set_port_if1_then (= egress_spec 0)))
(assert (=> (and set_port_if1_else vrf_ip_to_port0) (= egress_spec 1)))
(assert (=> (and set_port_if1_else vrf_ip_to_port1) (= egress_spec 2)))
(assert (=> (and set_port_if1_else vrf_ip_to_port2) (= egress_spec 3)))
(assert (=>
    (and (not vrf_ip_to_port0) (not vrf_ip_to_port1) (not vrf_ip_to_port2))
    (= egress_spec -1)
))

;; what does not being dropped mean in this program
(define-fun not_dropped () Bool (not (= egress_spec -1)))

;; Optimization/Idea to consider:
;; perhaps setting vrf and egress_spec to -1 is not needed as an assert
;; but only as part of the not_dropped or other similar aliases?
;; this means that the smt solver will not need to assert it for
;; complete queries, which will be valid by definition, and only
;; assert them (and have to do more work) for some of the partial
;; queries.

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
(assert (and port_to_vrf1 vrf_ip_to_port2 set_port_if1_then))
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 6")
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
