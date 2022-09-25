(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (str.to.re "Z>")))
(assert (> (str.to.int x) (str.len m)))
(assert (= 2 (str.len n)))
(assert (= (str.len y) 3))
(check-sat)
(get-model)
