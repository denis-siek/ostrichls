(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "1") (str.to.re "d")))))
(assert (= 0 (str.len x)))
(check-sat)
(get-model)
