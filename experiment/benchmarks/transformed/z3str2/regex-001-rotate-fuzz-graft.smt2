(declare-const x String)
(declare-const y String)
(assert (= x ""))
(assert (str.in.re x (str.to.re "FpSv{z''\t''z6")))
(check-sat)
(get-model)
