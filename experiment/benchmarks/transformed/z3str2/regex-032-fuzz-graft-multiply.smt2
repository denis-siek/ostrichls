(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (str.to.re "yyTTcc")))
(assert (= (str.to.int x) (str.to.int m)))
(check-sat)
(get-model)
