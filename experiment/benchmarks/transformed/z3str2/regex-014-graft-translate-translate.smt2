(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "d'\n'")))
(assert (str.in.re y (re.* (re.* (str.to.re "d'\n'")))))
(assert (= (str.len x) 2))
(assert (= 4 (str.len y)))
(check-sat)
(get-model)
