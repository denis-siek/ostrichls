(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "^'''\n'''")))
(assert (str.in.re y (str.to.re "^'''\n'''")))
(assert (= (str.len x) 4))
(assert (= 2 (str.len y)))
(check-sat)
(get-model)
