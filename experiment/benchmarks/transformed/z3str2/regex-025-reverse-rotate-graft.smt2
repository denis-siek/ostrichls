(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "a") (re.* (str.to.re "b"))))))
(assert (str.in.re y (re.* (re.++ (re.* (str.to.re "b")) (str.to.re "a")))))
(assert (= 7 (str.len y)))
(assert (not (= x y)))
(assert (= (str.len x) (str.len x)))
(check-sat)
(get-model)
