(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "s"))))
(assert (str.in.re y (str.to.re ",$~jLnK[%+9''\r''I]X")))
(assert (= 3 (str.to.int x)))
(assert (= (str.len y) 2))
(check-sat)
(get-model)
