(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ y x) (str.++ n m)))
(assert (str.in.re n (re.* (str.to.re "b"))))
(assert (> (str.to.int x) (str.to.int m)))
(assert (= 0 (str.to.int n)))
(assert (= 1 (str.len y)))
(check-sat)
(get-model)
