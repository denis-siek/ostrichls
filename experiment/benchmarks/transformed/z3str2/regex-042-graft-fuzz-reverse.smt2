(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "a") (str.to.re "c"))))
(assert (str.in.re x (re.union (str.to.re "a") (re.++ (re.* (re.* (str.to.re ""))) (re.* (str.to.re ""))))))
(assert (= (str.to.int x) 4))
(check-sat)
(get-model)
