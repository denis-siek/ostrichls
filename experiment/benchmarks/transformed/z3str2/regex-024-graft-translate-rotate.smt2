(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "w")) (str.to.re """")))))
(assert (str.in.re y (re.* (re.++ (str.to.re """") (re.* (str.to.re "w"))))))
(check-sat)
(get-model)
