(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.+ (str.to.re ",pj$}''' '''ab")))))
(assert (str.in.re x (str.to.re "aba")))
(assert (str.in.re x (str.to.re "ab")))
(assert (> (str.len x) 2))
(check-sat)
(get-model)
