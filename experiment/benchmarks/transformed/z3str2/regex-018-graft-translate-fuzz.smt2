(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "23")))
(assert (= (str.to.int x) 0))
(assert (not (= x ")xI'\r'Lc'u'\x0c''\r':B!]")))
(check-sat)
(get-model)
