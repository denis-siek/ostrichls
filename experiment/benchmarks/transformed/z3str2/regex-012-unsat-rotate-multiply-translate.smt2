(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "XXUUffpp") (str.to.re "112233")))))
(assert (= 10 (str.len x)))
(check-sat)
(get-model)
