(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "L") (re.* (str.to.re "x"))))))
(assert (> (str.len x) 0))
(check-sat)
(get-model)
