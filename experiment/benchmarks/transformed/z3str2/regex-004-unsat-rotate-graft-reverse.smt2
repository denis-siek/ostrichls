(declare-const x String)
(assert (= x "edcdcba"))
(assert (str.in.re x (str.to.re "dcba")))
(check-sat)
(get-model)
