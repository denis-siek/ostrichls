(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "^") (re.* (str.to.re "r"))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "^") (re.* (str.to.re "r"))))))
(check-sat)
(get-model)
