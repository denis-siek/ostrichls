(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "r")) (str.to.re "y")))))
(assert (str.in.re y (re.* (re.++ (re.* (str.to.re "r")) (str.to.re "y")))))
(check-sat)
(get-model)
