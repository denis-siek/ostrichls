(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "Z") (re.* (str.to.re "b"))))))
(assert (str.in.re y (re.* (re.union (str.to.re "a") (re.* (str.to.re "b"))))))
(assert (not (= x y)))
(assert (= (str.to.int x) (str.len y)))
(check-sat)
(get-model)
