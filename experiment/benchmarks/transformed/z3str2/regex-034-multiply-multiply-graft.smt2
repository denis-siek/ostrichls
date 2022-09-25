(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (str.to.re "aaaabbbbcccc")))
(assert (> (str.len x) (str.len m)))
(assert (= 12 (str.len n)))
(assert (= (str.len y) 4))
(check-sat)
(get-model)
