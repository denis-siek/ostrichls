(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (re.* (str.to.re "")) (str.to.re "r")))))
(assert (= (str.len x) 2))
(check-sat)
(get-model)
