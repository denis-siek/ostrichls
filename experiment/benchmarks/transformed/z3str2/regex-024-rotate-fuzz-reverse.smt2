(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "a") (re.* (str.to.re "b"))))))
(assert (str.in.re y (re.* (re.union (re.+ (str.to.re "q")) (str.to.re "a")))))
(check-sat)
(get-model)
