(declare-const x String)
(declare-const y String)
(assert (= x "HHHHHHHHH"))
(assert (str.in.re x (re.* (re.* (str.to.re "=ooqoo'\x0c'")))))
(check-sat)
(get-model)
