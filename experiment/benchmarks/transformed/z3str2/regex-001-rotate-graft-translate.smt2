(declare-const x String)
(declare-const y String)
(assert (= x ""))
(assert (str.in.re x (str.to.re "<d_")))
(check-sat)
(get-model)
