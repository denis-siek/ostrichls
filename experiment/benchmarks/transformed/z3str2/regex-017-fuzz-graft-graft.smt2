(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "32i;1")))
(assert (= 2 (str.to.int x)))
(check-sat)
(get-model)
