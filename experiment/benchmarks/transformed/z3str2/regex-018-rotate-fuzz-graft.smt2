(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "'' ''2]^"))))
(assert (= (str.len x) 1))
(assert (not (= x "ThxA")))
(check-sat)
(get-model)
