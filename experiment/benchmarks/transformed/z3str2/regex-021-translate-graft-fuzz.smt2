(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re ""))))
(assert (= 2 (str.to.int x)))
(check-sat)
(get-model)
