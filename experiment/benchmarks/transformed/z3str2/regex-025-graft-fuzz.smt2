(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.+ (re.union (re.+ (str.to.re "a")) (str.to.re ">"))) (str.to.re "d")))))
(assert (str.in.re y (re.+ (str.to.re ""))))
(assert (= (str.len x) 0))
(assert (not (= x y)))
(assert (= (str.to.int x) (str.len y)))
(check-sat)
(get-model)
