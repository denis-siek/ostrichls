(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "=") (re.* (str.to.re "C"))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "=") (re.* (str.to.re "C"))))))
(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))
(check-sat)
(get-model)
