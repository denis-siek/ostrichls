(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (re.* (str.to.re "")) (re.++ (re.+ (str.to.re "^^")) (str.to.re "bb"))))))
(assert (str.in.re y (re.* (str.to.re "bb"))))
(check-sat)
(get-model)
