(declare-const x String)
(assert (= (str.len x) 8))
(assert (str.in.re x (re.* (str.to.re "}/'\x0b'"))))
(assert (str.in.re x (re.* (str.to.re "yd}'\x0b'"))))
(check-sat)
(get-model)
