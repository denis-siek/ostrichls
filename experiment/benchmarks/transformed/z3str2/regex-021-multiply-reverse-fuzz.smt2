(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "o<b") (re.* (str.to.re "a"))))))
(assert (= (str.len x) 6))
(check-sat)
(get-model)
