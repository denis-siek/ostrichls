(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "iiuu"))))
(assert (str.in.re x (re.* (str.to.re "iiuuiiuu"))))
(assert (str.in.re x (re.* (str.to.re "iiuuiiuuii``"))))
(assert (> (str.len x) 2))
(check-sat)
(get-model)
