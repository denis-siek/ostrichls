(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.* (str.to.re "abcd"))))
(assert (= 8 (str.len y)))
(check-sat)
(get-model)
