(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "219"))))
(assert (str.in.re y (re.+ (re.+ (str.to.re "c]")))))
(assert (= (str.to.int x) 7))
(assert (= (str.len y) 4))
(check-sat)
(get-model)
