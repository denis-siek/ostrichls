(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "p"))))
(assert (> 0 (str.len x)))
(check-sat)
(get-model)
