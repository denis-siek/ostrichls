(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "T"))))
(assert (= 5 (str.len x)))
(assert (not (= x "TTTTT")))
(check-sat)
(get-model)
