(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "F"))))
(assert (= 1 (str.to.int x)))
(assert (not (= x "F")))
(check-sat)
(get-model)
