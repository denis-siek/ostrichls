(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.* (str.to.re "aahh")))))
(assert (str.in.re y (str.to.re "aahh")))
(assert (= (str.len x) (str.len y)))
(assert (= 4 8))
(check-sat)
(get-model)
