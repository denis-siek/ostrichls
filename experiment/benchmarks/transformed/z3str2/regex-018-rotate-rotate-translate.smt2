(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "zE") (str.to.re "123")))))
(assert (= 5 (str.len x)))
(assert (not (= x "123zE")))
(check-sat)
(get-model)
