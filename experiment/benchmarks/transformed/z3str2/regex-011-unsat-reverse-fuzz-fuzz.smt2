(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "Te7"))))
(assert (str.in.re y (re.* (str.to.re "VU"))))
(assert (= (str.to.int x) 3))
(check-sat)
(get-model)
