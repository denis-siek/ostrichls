(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (re.+ (str.to.re "b")) (str.to.re ""))))
(assert (str.in.re x (re.union (re.++ (str.to.re "a") (re.+ (str.to.re "5"))) (re.+ (str.to.re "")))))
(assert (= (str.len x) 0))
(check-sat)
(get-model)
