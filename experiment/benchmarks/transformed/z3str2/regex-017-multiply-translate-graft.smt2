(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "::RR") (str.to.re "**nn^^;;")))))
(assert (= (str.len x) 10))
(check-sat)
(get-model)
