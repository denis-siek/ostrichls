(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "C"))))
(assert (str.in.re y (re.* (str.to.re ")[B"))))
(assert (= (str.to.int x) 2))
(assert (= (str.to.int y) 1))
(check-sat)
(get-model)
