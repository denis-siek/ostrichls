(declare-const x String)
(declare-const y String)
(assert (= x ",,,,,,,,,"))
(assert (str.in.re x (str.to.re "SWU")))
(check-sat)
(get-model)
