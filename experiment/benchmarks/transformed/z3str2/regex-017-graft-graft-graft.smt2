(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "AB")))
(assert (= (str.len x) 5))
(check-sat)
(get-model)
