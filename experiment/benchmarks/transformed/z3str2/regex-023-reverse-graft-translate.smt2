(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "x")))
(assert (> 0 (str.len x)))
(check-sat)
(get-model)
