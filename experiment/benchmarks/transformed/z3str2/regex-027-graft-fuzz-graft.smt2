(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "z")))
(assert (= (str.to.int x) 4))
(assert (not (= x "a")))
(assert (not (= x "ab")))
(assert (not (= x "b")))
(check-sat)
(get-model)
