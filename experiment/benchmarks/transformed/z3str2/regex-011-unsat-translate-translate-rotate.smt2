(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "+'cv"))))
(assert (str.in.re y (re.* (str.to.re "+'cv"))))
(assert (= (str.len x) 6))
(check-sat)
(get-model)
