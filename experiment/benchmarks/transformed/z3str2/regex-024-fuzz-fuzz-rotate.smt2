(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.+ (str.to.re "b")) (str.to.re "")))))
(assert (str.in.re y (re.+ (re.union (re.* (str.to.re "")) (str.to.re "F")))))
(check-sat)
(get-model)
