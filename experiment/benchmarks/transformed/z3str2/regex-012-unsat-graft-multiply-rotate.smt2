(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "aabbccdd"))))
(assert (= (str.len x) 10))
(check-sat)
(get-model)
