(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (str.to.re "4Zuc")))
(assert (> (str.len x) (str.to.int m)))
(assert (= (str.len y) (str.to.int n)))
(assert (= 1 2))
(check-sat)
(get-model)
