(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.* (str.to.re "ddccbbaa")))))
(assert (str.in.re y (str.to.re "ddccbbaa")))
(assert (= 12 (str.len x)))
(check-sat)
(get-model)
