(declare-const x String)
(assert (= x "{/,zNE5u$>Taec"))
(assert (str.in.re x (str.to.re "jmR")))
(check-sat)
(get-model)
