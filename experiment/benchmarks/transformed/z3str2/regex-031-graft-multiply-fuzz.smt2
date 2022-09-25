(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (str.to.re "ab[1juBU""'\x0b''\t'*2")))
(assert (> (str.len x) (str.len m)))
(check-sat)
(get-model)
