(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.+ (str.to.re "RC(zJ:sb|l#I<I[=m#")))))
(assert (str.in.re x (str.to.re "X93@")))
(assert (> 38 22))
(assert (< (str.len x) (str.len x)))
(check-sat)
(get-model)
