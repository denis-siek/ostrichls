(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "ba")))
(assert (str.in.re y (re.* (re.* (str.to.re "ba")))))
(assert (= (str.len x) (str.len y)))
(assert (= 2 4))
(check-sat)
(get-model)
