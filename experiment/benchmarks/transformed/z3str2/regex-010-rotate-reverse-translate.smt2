(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "M>"))))
(assert (str.in.re x (re.* (str.to.re "M>M>"))))
(assert (str.in.re x (re.* (str.to.re "H>M>M>"))))
(check-sat)
(get-model)
