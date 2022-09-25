(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (re.* (str.to.re "CY")) (str.to.re "b")))))
(assert (= (str.to.int x) 8))
(assert (not (= x "M''\x0b''/qbb")))
(assert (not (= x "q,F''\r''u]")))
(check-sat)
(get-model)
