(declare-const x String)
(assert (= x "'\n''\n'WWss^^""""'\n''\n'WW'\n''\n'WWss"))
(assert (str.in.re x (re.* (re.union (str.to.re "^^""""'\n''\n'WW") (str.to.re "'\n''\n'WWss")))))
(check-sat)
(get-model)
