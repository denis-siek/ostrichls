(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "SS")))
(assert (= 4 (str.len x)))
(check-sat)
(get-model)
