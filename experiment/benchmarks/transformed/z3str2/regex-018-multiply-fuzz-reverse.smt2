(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "332=~4") (str.to.re "]Q1w5")))))
(assert (= 11 (str.len x)))
(assert (not (= x "QQaPryR,BAA21")))
(check-sat)
(get-model)
