(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "AAAABBBB") (str.to.re "aaaabbbbccccdddd")))))
(assert (= (str.len x) 20))
(check-sat)
(get-model)
