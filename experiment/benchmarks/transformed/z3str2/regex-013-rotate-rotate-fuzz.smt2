(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.+ (re.+ (str.to.re "Hd")))))
(assert (= (str.to.int y) 0))
(check-sat)
(get-model)
