(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re ""))))
(assert (str.in.re y (re.+ (str.to.re "5"))))
(assert (= (str.to.int x) 4))
(assert (= (str.to.int y) 0))
(check-sat)
(get-model)
