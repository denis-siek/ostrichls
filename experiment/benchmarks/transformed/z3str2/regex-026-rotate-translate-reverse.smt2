(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "C") (re.* (str.to.re "J"))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "C") (re.* (str.to.re "J"))))))
(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))
(check-sat)
(get-model)
