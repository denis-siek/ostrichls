(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "b") (re.* (str.to.re "a"))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "b") (re.* (str.to.re "a"))))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.len x) 7))
(check-sat)
(get-model)
