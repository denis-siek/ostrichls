(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "YY") (re.* (str.to.re "bb")))))
(assert (str.in.re x (re.++ (re.union (re.* (str.to.re "aa")) (re.* (str.to.re ""))) (str.to.re ""))))
(assert (= 6 (str.len x)))
(check-sat)
(get-model)
