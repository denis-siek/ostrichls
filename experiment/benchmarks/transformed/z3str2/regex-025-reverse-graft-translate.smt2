(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "r") (re.* (str.to.re "'\r'"))))))
(assert (str.in.re y (re.* (str.to.re "'\r'"))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= 7 (str.len x)))
(check-sat)
(get-model)
