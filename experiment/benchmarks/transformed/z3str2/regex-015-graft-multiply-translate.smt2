(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "ww'\x0c''\x0c'1122")))
(assert (str.in.re y (re.* (re.* (re.* (str.to.re "ww'\x0c''\x0c'1122"))))))
(assert (= (str.len x) (str.len y)))
(assert (= 8 16))
(check-sat)
(get-model)
