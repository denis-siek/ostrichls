(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "s") (re.* (str.to.re "8"))))))
(assert (> 0 (str.to.int x)))
(check-sat)
(get-model)
