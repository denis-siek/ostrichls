(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "==kk"))))
(assert (str.in.re x (re.* (str.to.re "==kk==kk"))))
(assert (str.in.re x (re.* (str.to.re "==kk==kk==SS"))))
(check-sat)
(get-model)
