(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "&b"))))
(assert (str.in.re y (str.to.re "&b")))
(assert (= (str.len x) 2))
(assert (= 4 (str.len y)))
(check-sat)
(get-model)
