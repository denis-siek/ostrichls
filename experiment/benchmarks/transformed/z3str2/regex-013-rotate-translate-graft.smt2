(declare-const x String)
(declare-const y String)
(assert (str.in.re y (str.to.re "|&j:")))
(assert (= 8 (str.len y)))
(check-sat)
(get-model)
