(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "S''\t''") (str.to.re "321")))))
(assert (= 5 (str.len x)))
(assert (not (= x "S''\t''321")))
(check-sat)
(get-model)
