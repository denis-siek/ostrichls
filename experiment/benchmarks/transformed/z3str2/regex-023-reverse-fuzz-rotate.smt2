(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "3") (re.* (str.to.re "b"))))))
(assert (> (str.to.int x) 0))
(check-sat)
(get-model)
