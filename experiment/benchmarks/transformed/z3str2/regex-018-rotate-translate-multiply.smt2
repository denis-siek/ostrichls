(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "'''\r''\r'''__") (str.to.re "112233")))))
(assert (= 10 (str.len x)))
(assert (not (= x "112233'''\r''\r'''__")))
(check-sat)
(get-model)
