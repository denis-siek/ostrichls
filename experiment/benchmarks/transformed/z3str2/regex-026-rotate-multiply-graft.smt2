(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "aa") (str.to.re "aa")))))
(assert (str.in.re y (re.* (re.++ (re.* (str.to.re "bb")) (re.* (str.to.re "bb"))))))
(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))
(check-sat)
(get-model)
