(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "a")) (str.to.re "]")))))
(assert (str.in.re y (re.* (re.union (re.* (str.to.re "b")) (str.to.re "a")))))
(check-sat)
(get-model)
