(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "EE") (re.* (str.to.re "bb"))))))
(assert (> 0 (str.len x)))
(check-sat)
(get-model)
