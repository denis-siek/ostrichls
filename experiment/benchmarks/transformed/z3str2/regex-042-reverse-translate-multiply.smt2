(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.* (str.to.re "II")) (str.to.re "WW"))))
(assert (str.in.re x (re.++ (re.++ (re.* (str.to.re "&&")) (re.* (str.to.re "II"))) (str.to.re "WW"))))
(assert (= 6 (str.len x)))
(check-sat)
(get-model)
