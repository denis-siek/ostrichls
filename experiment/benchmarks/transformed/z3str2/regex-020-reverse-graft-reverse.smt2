(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "b") (re.* (str.to.re "a"))))))
(assert (= 3 (str.len x)))
(assert (not (= x "abb")))
(assert (not (= x "bab")))
(assert (not (= x "aab")))
(check-sat)
(get-model)
