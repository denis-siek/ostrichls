(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re (str.++ y x) (str.to.re "c\\&a")))
(check-sat)
(get-model)
