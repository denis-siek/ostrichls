(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "ab"))))
(assert (str.in.re x (re.* (str.to.re "abab"))))
(assert (str.in.re x (str.to.re "ababac")))
(assert (> 1 (str.len x)))
(check-sat)
(get-model)
