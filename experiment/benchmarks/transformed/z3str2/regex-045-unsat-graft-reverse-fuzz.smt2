(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (not (str.in.re x (str.to.re ")a"))))
(assert (= x "b'\r'Rq"))
(check-sat)
(get-model)
