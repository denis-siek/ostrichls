(declare-const x String)
(declare-const y String)
(assert (= x ""))
(assert (str.in.re x (str.to.re "7W_u'' ''")))
(check-sat)
(get-model)
