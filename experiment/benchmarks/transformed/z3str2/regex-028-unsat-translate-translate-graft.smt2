(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "-W"))))
(assert (str.in.re x (re.* (re.* (str.to.re "-W-W-I")))))
(assert (str.in.re x (str.to.re "-W-W")))
(assert (> 1 (str.len x)))
(check-sat)
(get-model)
