(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "BA") (str.to.re "321")))))
(assert (= (str.len x) 5))
(check-sat)
(get-model)
