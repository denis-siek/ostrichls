(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "}"))))
(assert (str.in.re x (re.* (str.to.re "a"))))
(assert (str.in.re x (re.+ (str.to.re "v$)>'bV`u@"))))
(check-sat)
(get-model)
