(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.* (re.+ (str.to.re "dd")))))
(assert (= (str.to.int y) 30))
(check-sat)
(get-model)
