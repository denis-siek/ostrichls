(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "ll^^"))))
(assert (str.in.re x (re.* (str.to.re "ll^^ll^^"))))
(assert (str.in.re x (re.* (str.to.re "ll^^ll^^llpp"))))
(assert (> (str.len x) 2))
(check-sat)
(get-model)
