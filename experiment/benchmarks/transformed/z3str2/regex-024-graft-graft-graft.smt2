(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "b")))
(assert (str.in.re y (re.* (re.++ (str.to.re "a") (str.to.re "b")))))
(check-sat)
(get-model)
