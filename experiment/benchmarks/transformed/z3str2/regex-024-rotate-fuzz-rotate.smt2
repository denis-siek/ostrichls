(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "a")) (str.to.re "b")))))
(assert (str.in.re y (re.* (re.union (re.+ (str.to.re "a")) (str.to.re "q")))))
(check-sat)
(get-model)
