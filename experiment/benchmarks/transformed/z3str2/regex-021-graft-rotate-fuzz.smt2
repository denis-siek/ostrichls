(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "a") (re.* (str.to.re "1"))))))
(assert (= 3 (str.len x)))
(check-sat)
(get-model)
