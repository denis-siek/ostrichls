(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "abcd"))))
(assert (str.in.re x (str.to.re "abcdabcd")))
(assert (> 20 (str.len x)))
(assert (< (str.len x) 25))
(check-sat)
(get-model)
