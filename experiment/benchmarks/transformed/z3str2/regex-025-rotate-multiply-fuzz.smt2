(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (re.+ (str.to.re "")) (str.to.re "yK")))))
(assert (str.in.re y (re.+ (re.++ (re.+ (str.to.re "b$")) (str.to.re "a")))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.len x) 28))
(check-sat)
(get-model)
