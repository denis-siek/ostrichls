(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.* (str.to.re "21ba")))))
(assert (str.in.re y (re.* (str.to.re "21ba"))))
(assert (= (str.len x) 4))
(assert (= 8 (str.len y)))
(check-sat)
(get-model)
