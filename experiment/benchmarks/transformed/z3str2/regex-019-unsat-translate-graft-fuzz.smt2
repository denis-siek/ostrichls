(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "6")))
(assert (= (str.len x) 8))
(assert (not (= x "iii")))
(check-sat)
(get-model)
