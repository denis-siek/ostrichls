(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "123")))
(assert (= (str.len x) 5))
(assert (not (= x "123*j")))
(check-sat)
(get-model)
