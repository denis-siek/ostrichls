(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "' '''.v0}'\r'h-'\r'(fcF'\x0b'9['\x0c'.E@'sG9C'\x0b'd*")))
(assert (str.in.re x (re.+ (re.+ (str.to.re "2'' '''' '0w1F")))))
(assert (> 14 32))
(assert (< (str.to.int x) (str.to.int x)))
(check-sat)
(get-model)
