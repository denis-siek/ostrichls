(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "ddddccccbbbbaaaa"))))
(assert (str.in.re y (re.* (str.to.re "ddddccccbbbbaaaa"))))
(assert (= (str.len x) 24))
(check-sat)
(get-model)
