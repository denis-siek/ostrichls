(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "a")) (str.to.re "<")))))
(assert (str.in.re y (re.+ (re.union (re.+ (str.to.re "")) (str.to.re "b")))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.to.int x) 13))
(check-sat)
(get-model)
