(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.+ (str.to.re "")) (str.to.re "bW")))))
(assert (str.in.re y (re.* (re.union (re.* (str.to.re "r")) (str.to.re "Z")))))
(assert (not (= x y)))
(assert (= (str.to.int x) (str.len y)))
(check-sat)
(get-model)
