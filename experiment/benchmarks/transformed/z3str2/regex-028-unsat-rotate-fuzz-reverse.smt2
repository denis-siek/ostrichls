(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "b"))))
(assert (str.in.re x (re.+ (str.to.re "a;{"))))
(assert (str.in.re x (re.+ (str.to.re "ca'KPa'Ha""Z""F!"))))
(assert (> (str.len x) 1))
(check-sat)
(get-model)
