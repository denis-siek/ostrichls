(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.* (re.* (str.to.re "ab12"))))))
(assert (str.in.re y (str.to.re "ab12")))
(assert (= (str.len x) 4))
(assert (= 8 (str.len y)))
(check-sat)
(get-model)
