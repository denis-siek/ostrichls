(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (re.* (str.to.re "aaaaaaaabbbbbbbbcccccccc"))))
(assert (> (str.len x) (str.len m)))
(assert (= 24 (str.len n)))
(assert (= 8 (str.len y)))
(check-sat)
(get-model)
