(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "")))
(assert (= 4 (str.to.int x)))
(assert (not (= x "b")))
(assert (not (= x "b")))
(check-sat)
(get-model)
