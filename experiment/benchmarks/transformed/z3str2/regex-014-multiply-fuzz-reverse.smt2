(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "bbaUjZ5"))))
(assert (str.in.re y (re.+ (str.to.re "ba"))))
(assert (= (str.len x) 0))
(assert (= (str.to.int y) 14))
(check-sat)
(get-model)
