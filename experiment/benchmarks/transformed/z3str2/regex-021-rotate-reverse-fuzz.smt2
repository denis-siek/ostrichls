(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "a") (re.+ (str.to.re ""))))))
(assert (= (str.len x) 3))
(check-sat)
(get-model)
