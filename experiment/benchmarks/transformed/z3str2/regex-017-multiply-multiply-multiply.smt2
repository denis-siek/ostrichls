(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "AAAAAAAABBBBBBBB") (re.union (str.to.re "aaaaaaaabbbbbbbbccccccccdddddddd") (str.to.re "111111112222222233333333"))))))
(assert (= 40 (str.len x)))
(check-sat)
(get-model)
