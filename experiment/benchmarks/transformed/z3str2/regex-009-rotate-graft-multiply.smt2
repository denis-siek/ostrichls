(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.* (str.to.re "aabbccddaabbccdd")))))
(assert (str.in.re x (str.to.re "aabbccdd")))
(assert (> (str.len x) (str.len x)))
(assert (< 40 50))
(check-sat)
(get-model)
