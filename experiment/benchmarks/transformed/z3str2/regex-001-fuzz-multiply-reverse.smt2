(declare-const x String)
(declare-const y String)
(assert (= x ""))
(assert (str.in.re x (re.+ (str.to.re "RR''''\n''''\n''''ee"))))
(check-sat)
(get-model)
