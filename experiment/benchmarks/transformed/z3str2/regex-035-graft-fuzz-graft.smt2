(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re (str.++ x y) (str.to.re ")VCc")))
(check-sat)
(get-model)
