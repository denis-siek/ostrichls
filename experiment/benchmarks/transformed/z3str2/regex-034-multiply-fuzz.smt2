(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (re.+ (str.to.re "ab*b'$Lc"))))
(assert (> (str.len x) (str.len m)))
(assert (= 0 (str.to.int n)))
(assert (= 2 (str.len y)))
(check-sat)
(get-model)
