(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (not (str.in.re x (str.to.re "'\x0c'=U"))))
(assert (= x "'\x0c'=U"))
(check-sat)
(get-model)
