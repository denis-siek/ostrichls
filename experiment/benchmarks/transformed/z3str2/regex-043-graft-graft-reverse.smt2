(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (str.to.re "a")))
(assert (= 3 (str.len x)))
(assert (not (= x "bba")))
(assert (not (= x "aba")))
(assert (not (= x "abb")))
(assert (not (= x "bbb")))
(assert (not (= x "aab")))
(assert (not (= x "bab")))
(assert (not (= x "aaa")))
(check-sat)
(get-model)
