(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "w") (re.* (str.to.re """"))))))
(assert (str.in.re y (re.* (re.++ (re.* (str.to.re """")) (str.to.re "w")))))
(check-sat)
(get-model)
