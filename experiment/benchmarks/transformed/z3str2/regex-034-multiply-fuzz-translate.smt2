(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (re.+ (str.to.re "}'\x0c'L|<-"))))
(assert (> (str.to.int x) (str.len m)))
(assert (= 11 (str.len n)))
(assert (= 2 (str.to.int y)))
(check-sat)
(get-model)
