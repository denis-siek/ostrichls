(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "bbdd"))))
(assert (str.in.re y (str.to.re "aabbccGG]]")))
(assert (= 20 (str.len x)))
(check-sat)
(get-model)
