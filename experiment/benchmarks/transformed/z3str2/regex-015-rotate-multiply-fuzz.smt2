(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "GlZUa.[e'\n'\\^C]REb\\;t>QT112"))))
(assert (str.in.re y (re.* (re.+ (str.to.re "aaa'\t''\t'%-&iEK' '3.T1it4Q' 'ub2")))))
(assert (= (str.to.int x) 6))
(assert (= (str.to.int y) 21))
(check-sat)
(get-model)
