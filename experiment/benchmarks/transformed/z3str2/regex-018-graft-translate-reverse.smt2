(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "321")))
(assert (= (str.len x) 5))
(assert (not (= x "j*321")))
(check-sat)
(get-model)
