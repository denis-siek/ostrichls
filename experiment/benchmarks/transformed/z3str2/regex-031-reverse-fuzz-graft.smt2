(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ y x) (str.++ n m)))
(assert (str.in.re n (str.to.re "[&Wa")))
(assert (> (str.len x) (str.len m)))
(check-sat)
(get-model)
