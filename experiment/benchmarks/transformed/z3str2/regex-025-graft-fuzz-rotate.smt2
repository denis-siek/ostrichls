(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "b") (str.to.re "b")))))
(assert (str.in.re y (re.+ (re.++ (re.* (re.* (str.to.re "a"))) (str.to.re "")))))
(assert (= (str.to.int x) (str.len y)))
(assert (not (= x y)))
(assert (= 11 (str.len x)))
(check-sat)
(get-model)
