(declare-const x String)
(declare-const y String)
(assert (= x ""))
(assert (str.in.re x (re.+ (str.to.re "(xS"))))
(check-sat)
(get-model)
