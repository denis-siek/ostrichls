(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "12d*"))))
(assert (= (str.len x) 9))
(check-sat)
(get-model)
