(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "eett"))))
(assert (str.in.re x (re.* (re.* (str.to.re "eetteetteeSS")))))
(assert (str.in.re x (str.to.re "eetteett")))
(check-sat)
(get-model)
