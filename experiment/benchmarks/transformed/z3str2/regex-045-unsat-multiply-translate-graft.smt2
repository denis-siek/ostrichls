(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (not (str.in.re x (str.to.re "RRSS>>"))))
(assert (= x "RRSS>>"))
(check-sat)
(get-model)
