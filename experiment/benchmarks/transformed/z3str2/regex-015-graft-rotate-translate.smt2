(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "*+12")))
(assert (str.in.re y (re.* (re.* (re.* (str.to.re "*+12"))))))
(assert (= (str.len x) (str.len y)))
(assert (= 4 8))
(check-sat)
(get-model)
