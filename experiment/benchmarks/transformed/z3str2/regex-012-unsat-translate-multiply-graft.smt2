(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "**LL((''''\x0b''''\x0b''''")))
(assert (= (str.len x) 10))
(check-sat)
(get-model)
