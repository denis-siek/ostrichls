(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "**LL((''''\x0b''''\x0b''''") (str.to.re "112233")))))
(assert (= 10 (str.len x)))
(check-sat)
(get-model)
