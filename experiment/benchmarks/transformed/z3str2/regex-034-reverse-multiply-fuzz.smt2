(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ y x) (str.++ n m)))
(assert (str.in.re n (re.+ (str.to.re "cb'\x0c'B-^"))))
(assert (> (str.len x) (str.to.int m)))
(assert (= 1 (str.to.int n)))
(assert (= 3 (str.len y)))
(check-sat)
(get-model)
