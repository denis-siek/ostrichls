(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "KK<<"))))
(assert (str.in.re x (re.* (str.to.re "KK<<KK<<"))))
(assert (str.in.re x (re.* (str.to.re "KK<<KK<<KKii"))))
(assert (> (str.len x) 2))
(check-sat)
(get-model)
