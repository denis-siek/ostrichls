(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "aaaabbbb"))))
(assert (str.in.re x (re.* (str.to.re "aaaabbbbaaaabbbb"))))
(assert (str.in.re x (re.* (str.to.re "aaaabbbbaaaabbbbaaaacccc"))))
(check-sat)
(get-model)
