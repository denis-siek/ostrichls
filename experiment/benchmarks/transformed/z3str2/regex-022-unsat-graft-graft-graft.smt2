(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "a")))
(assert (= 2 (str.len x)))
(assert (not (= x "bb")))
(assert (not (= x "ab")))
(check-sat)
(get-model)
