(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (re.+ (str.to.re ""))))
(assert (> (str.to.int x) (str.len m)))
(assert (= 4 (str.to.int n)))
(assert (= 1 (str.len y)))
(check-sat)
(get-model)
