(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ y x) (str.++ n m)))
(assert (str.in.re n (re.* (str.to.re "UUaazz"))))
(assert (> (str.len x) (str.len m)))
(assert (= 6 (str.len n)))
(assert (= 2 (str.len y)))
(check-sat)
(get-model)
