(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "bb"))))
(assert (= 6 (str.len x)))
(assert (not (= x "aabbbb")))
(assert (not (= x "bbaabb")))
(assert (not (= x "aaaabb")))
(check-sat)
(get-model)
