(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "fe4")))
(check-sat)
(get-model)
