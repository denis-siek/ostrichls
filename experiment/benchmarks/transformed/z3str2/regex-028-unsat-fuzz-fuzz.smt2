(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re ")"))))
(assert (str.in.re x (re.* (str.to.re "wcJba"))))
(assert (str.in.re x (re.* (str.to.re "9OHX+*B.eQm}""2&c8+_c"))))
(assert (> (str.len x) 3))
(check-sat)
(get-model)
