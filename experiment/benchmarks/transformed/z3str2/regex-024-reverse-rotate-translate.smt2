(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "W") (re.* (str.to.re "v"))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "W") (re.* (str.to.re "v"))))))
(check-sat)
(get-model)
