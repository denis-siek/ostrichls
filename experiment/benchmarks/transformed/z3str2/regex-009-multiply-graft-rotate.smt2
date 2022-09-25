(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "aabbccddaabbccdd")))
(assert (str.in.re x (re.* (re.* (str.to.re "aabbccdd")))))
(assert (> 40 (str.len x)))
(assert (< (str.len x) 50))
(check-sat)
(get-model)
