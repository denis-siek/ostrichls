(declare-const x String)
(declare-const y String)
(assert (str.in.re y (str.to.re "`]A'''\x0c'''")))
(assert (= (str.len y) 8))
(check-sat)
(get-model)
