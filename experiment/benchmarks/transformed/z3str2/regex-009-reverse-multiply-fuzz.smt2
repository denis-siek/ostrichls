(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "d9-oc{[<gn4bxE}SV/:Z*Gp>""41a"))))
(assert (str.in.re x (re.* (str.to.re "dc>%,'\n'$'\r'9c3$x'V'\x0b'uFEQgNl'\x0c'' 'N'I^=%+{Da'\x0c'fF-"))))
(assert (> (str.len x) 76))
(assert (< (str.to.int x) 65))
(check-sat)
(get-model)
