(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "s"))))
(assert (str.in.re y (re.* (re.* (str.to.re ",$~jLnK[%+9''\r''I]X")))))
(assert (= (str.to.int x) 3))
(assert (= (str.len y) 2))
(check-sat)
(get-model)
