(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ y x) (str.++ n m)))
(assert (str.in.re n (str.to.re "HD'")))
(assert (> 1 (str.len m)))
(assert (= 3 (str.len n)))
(assert (= (str.len x) (str.len y)))
(check-sat)
(get-model)
