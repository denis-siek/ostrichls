(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "b") (str.to.re "b")))))
(assert (str.in.re y (re.* (re.++ (re.* (str.to.re "a")) (str.to.re "a")))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.len x) 7))
(check-sat)
(get-model)
