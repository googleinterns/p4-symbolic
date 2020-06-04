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

;; Define un-interpreted constants that constitute a packet
;; the exact definition should depend on the headers and
;; metadata defined/used in the p4 program.
;;
;; It is probably a good idea to keep the names of theses
;; constants similar to the attribute names from p4
;;
(declare-const ingress_port Int)

;; Define un-interpreted constants that constitute an output
;; packet. At the end of the program, we will define some
;; constraints on this constant guided by the program flow
;; and the table entries
(declare-const egress_spec Int)

;; Define an interpreted function (i.e. just an alias) per
;; row in the table.
;;
;; The body of the function uses the packet constants, such
;; the body is true iff the corresponding entry is hit by the
;; corresponding packet.
;;
;; The table definition should tell us which types to use and
;; what kind of logical operations should be performed (exact, LPM)
;; the values of the table entries can tell us what the concrete
;; values in these logical operations are.
;;
;; Later, we should consider using quantified variables instead
;; of values to abstract away from concrete table entries.
;;
;; These functions must be so that any given packet can only satisfy
;; no more than one function. An easy way to do this is to and
;; the function body with the negation of every other function.
;; that is probably inefficient, and can cause problems with cyclic
;; definitions. A better way is to do this by design, e.g. by taking
;; into consideration LPM and priorities inline.
;;
;; A good naming convention is to use the table name with the index
;; of the table entry
;;
;;
;; When parsing the p4 program, if we find table dependence (e.g. vrf)
;; then the dependent table functions should reference the depending
;; table functions in their body.
;;
;; This simple mechanism should be extended to handle entries
;; pointing to different actions and providing different parameters
;; actions likely do not need to be reflected here beyond as aliases
;; parameters are important depending on their use within the action
(define-fun ports_exact0 () Bool (= ingress_port 0))
(define-fun ports_exact1 () Bool (= ingress_port 1))

;; Any branching within the code should also be reflected here,
;; likely as function aliases similar to the above. For example,
;; an if statement with two branches should result in two functions
;; indicating which branch was taken.
;;
;; A branch's side effects likely need to be encoded in a way similar
;; to a table match side effect (e.g. params)
;;

;; We define restrictions/constraints on output attributes here,
;; this should also be done for other intermediate attributes
;; such as action inputs from table row matches.
;;
(assert (= egress_spec
    (ite ports_exact0 1
        (ite ports_exact1 0
            -1
        )
    )
))

;; We should define aliases for important properties/restrictions here.
;; Things like packet validity, not being dropped, etc.
;;
(define-fun not_dropped () Bool (not (= egress_spec -1)))

;; Finally, we need to have combinations of the above defined quantities
;; representing combinations of code paths and table hits.
;;
;; This should likely be generated via some cross-product like iteration
;; in our code, over all table entries from different tables and code branches,
;; guided by the parsed program trace/flow.
;;
;; For performance reasons, we should exclude clearly unreachable combinations.
;; For example, a table match that invokes an action with an if branch in a different
;; un-invoked action. However, not excluding them should not affect correctness,
;; the SMT solver should return unsat for such combinations
;;
(push)
(echo "combination 1")
(assert ports_exact0)
(check-sat)
(get-model)
(echo "")
(pop)

(push)
(echo "combination 2")
(assert ports_exact1)
(check-sat)
(get-model)
(echo "")
(pop)

;; Alternatively, we can ask for a packet that has output port 1
;;
(push)
(echo "output = 1")
(assert (= egress_spec 1))
(check-sat)
(get-model)
(echo "")
(pop)

;; Or, we can simulate what will happen to an input packet on port 1
(push)
(echo "input = 1")
(assert (= ingress_port 1))
(check-sat)
(get-model)
(echo "")
(pop)

;; Finally, we can determine if a packet is valid/not dropped, or ask
;; for an arbitrary valid one
(push)
(echo "Is packet with input port 5 valid/not-dropped?")
(assert (and (= ingress_port 5) not_dropped))
(check-sat)
(echo "")
(pop)

(push)
(echo "Get any valid/not dropped packet")
(assert not_dropped)
(check-sat)
(get-model)
(echo "")
(pop)



