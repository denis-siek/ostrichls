(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "<")))
(assert (= 2 (str.len x)))
(assert (not (= x "'''\n''''''\n'''")))
(assert (not (= x "<'''\n'''")))
(check-sat)
(get-model)
