(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "Ce5o"))))
(assert (str.in.re y (re.* (str.to.re "dL>"))))
(assert (= (str.to.int x) 3))
(check-sat)
(get-model)
