(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "ba")))
(assert (str.in.re y (re.* (str.to.re "ba"))))
(assert (= 4 (str.len y)))
(assert (= 2 (str.len x)))
(check-sat)
(get-model)
