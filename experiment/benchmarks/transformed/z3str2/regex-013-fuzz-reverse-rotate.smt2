(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.+ (re.+ (str.to.re "AvX7PJb0a")))))
(assert (= (str.len y) 3))
(check-sat)
(get-model)
