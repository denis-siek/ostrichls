(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "a"))))
(assert (= 2 (str.len x)))
(check-sat)
(get-model)
