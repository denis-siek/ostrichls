(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "ab)8-c")))
(check-sat)
(get-model)
