(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re (str.++ y x) (str.to.re "cb7JM")))
(check-sat)
(get-model)
