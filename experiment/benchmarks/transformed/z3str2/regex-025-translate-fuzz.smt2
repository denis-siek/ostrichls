(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "")) (str.to.re "*")))))
(assert (str.in.re y (re.* (re.++ (re.+ (str.to.re "")) (str.to.re "H")))))
(assert (= (str.len x) (str.to.int y)))
(assert (not (= x y)))
(assert (= (str.len x) 11))
(check-sat)
(get-model)
