(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "321")))
(assert (= (str.len x) 11))
(assert (not (= x "R|Q`321R|Q`")))
(assert (not (= x "321R|Q`R|Q`")))
(check-sat)
(get-model)
