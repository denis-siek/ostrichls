(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re """")) (str.to.re "w")))))
(assert (str.in.re y (re.* (re.++ (str.to.re "w") (re.* (str.to.re """"))))))
(check-sat)
(get-model)
