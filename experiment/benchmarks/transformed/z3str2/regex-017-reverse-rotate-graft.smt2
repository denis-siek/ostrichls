(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "BA")))
(assert (= (str.len x) 5))
(check-sat)
(get-model)
