(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "XX]]}}BB")))
(assert (= (str.len x) 10))
(check-sat)
(get-model)
