(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (str.to.re "abc")))
(assert (> (str.len x) (str.len m)))
(assert (= (str.len y) (str.len n)))
(assert (= 1 3))
(check-sat)
(get-model)
