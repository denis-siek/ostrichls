(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "aaaa")))
(assert (= 12 (str.len x)))
(assert (not (= x "aaaabbbbbbbb")))
(assert (not (= x "bbbbaaaabbbb")))
(assert (not (= x "aaaaaaaabbbb")))
(check-sat)
(get-model)
