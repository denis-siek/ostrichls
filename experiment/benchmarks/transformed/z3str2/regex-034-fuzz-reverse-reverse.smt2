(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (re.+ (str.to.re "4Zuc"))))
(assert (> (str.len x) (str.to.int m)))
(assert (= 1 (str.to.int n)))
(assert (= 2 (str.len y)))
(check-sat)
(get-model)
