(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "E") (str.to.re "b")))))
(assert (> 0 (str.len x)))
(check-sat)
(get-model)
