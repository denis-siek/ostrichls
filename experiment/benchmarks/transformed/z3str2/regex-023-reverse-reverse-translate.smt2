(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "s")) (str.to.re "^")))))
(assert (> (str.len x) 0))
(check-sat)
(get-model)
