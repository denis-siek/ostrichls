(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "mmVV") (str.to.re "11")))))
(assert (= 14 (str.len x)))
(assert (not (= x "1133@@")))
(check-sat)
(get-model)
