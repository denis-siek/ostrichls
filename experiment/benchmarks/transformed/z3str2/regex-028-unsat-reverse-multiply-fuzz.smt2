(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "bba"))))
(assert (str.in.re x (re.* (str.to.re "$,a0Hba"))))
(assert (str.in.re x (re.* (str.to.re "gMVkouVdpg&$UFNWCoaX19R|sr}aabYwU~F*z7a;[e'\t'"))))
(assert (> (str.to.int x) 4))
(check-sat)
(get-model)
