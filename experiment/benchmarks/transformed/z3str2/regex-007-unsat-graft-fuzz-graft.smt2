(declare-const x String)
(assert (= (str.len x) 5))
(assert (str.in.re x (str.to.re "ced")))
(assert (str.in.re x (re.* (re.* (str.to.re "a)")))))
(check-sat)
(get-model)
