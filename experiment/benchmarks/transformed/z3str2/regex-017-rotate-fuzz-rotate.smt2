(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "3") (re.++ (str.to.re "<Y") (str.to.re "aQt''\t''\\"))))))
(assert (= 9 (str.to.int x)))
(check-sat)
(get-model)
