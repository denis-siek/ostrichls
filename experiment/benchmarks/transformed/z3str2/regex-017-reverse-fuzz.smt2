(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "B") (re.++ (str.to.re "cbY") (str.to.re "31"))))))
(assert (= 8 (str.to.int x)))
(check-sat)
(get-model)
