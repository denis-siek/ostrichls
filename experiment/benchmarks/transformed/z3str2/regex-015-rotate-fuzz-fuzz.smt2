(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "2"))))
(assert (str.in.re y (re.* (re.+ (str.to.re "kn]EF?Pu")))))
(assert (= (str.len x) 0))
(assert (= (str.to.int y) 11))
(check-sat)
(get-model)
