(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "a+9kWtiWgccdd"))))
(assert (str.in.re y (re.+ (str.to.re "6u[)1VAWYIvq{:]d"))))
(assert (= (str.len x) 5))
(check-sat)
(get-model)
