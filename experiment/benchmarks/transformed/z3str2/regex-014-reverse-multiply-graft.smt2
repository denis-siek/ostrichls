(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "bbaa")))
(assert (str.in.re y (re.* (str.to.re "bbaa"))))
(assert (= 4 (str.len x)))
(assert (= (str.len y) 8))
(check-sat)
(get-model)
