(declare-const x String)
(declare-const y String)
(assert (= x "##################"))
(assert (str.in.re x (str.to.re "gg'''''\x0c''\x0c'''''WW")))
(check-sat)
(get-model)
