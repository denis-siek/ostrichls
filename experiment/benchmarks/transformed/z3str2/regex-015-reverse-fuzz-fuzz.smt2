(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "Z'\x0c'<VQp"))))
(assert (str.in.re y (re.+ (re.* (str.to.re "$5,")))))
(assert (= (str.to.int x) 2))
(assert (= (str.len y) 24))
(check-sat)
(get-model)
