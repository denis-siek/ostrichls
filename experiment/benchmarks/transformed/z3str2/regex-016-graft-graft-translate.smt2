(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "|y.-")))
(assert (= 11 (str.len x)))
(assert (not (= x "|y.-123|y.-")))
(assert (not (= x "|y.-|y.-123")))
(check-sat)
(get-model)
