(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "aaaaaaaabbbbbbbb"))))
(assert (str.in.re x (re.* (str.to.re "aaaaaaaabbbbbbbbaaaaaaaabbbbbbbb"))))
(assert (str.in.re x (re.* (str.to.re "aaaaaaaabbbbbbbbaaaaaaaabbbbbbbbaaaaaaaacccccccc"))))
(assert (> (str.len x) 8))
(check-sat)
(get-model)
