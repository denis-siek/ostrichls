(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "MbK"))))
(assert (str.in.re y (re.* (re.+ (str.to.re "8!~1")))))
(assert (= (str.to.int x) 5))
(assert (= (str.to.int y) 11))
(check-sat)
(get-model)
