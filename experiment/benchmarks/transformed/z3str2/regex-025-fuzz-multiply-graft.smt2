(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.* (str.to.re "aa")) (str.to.re "bb")))))
(assert (str.in.re y (re.+ (re.union (str.to.re "bb") (re.* (str.to.re "aa"))))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= 0 (str.len x)))
(check-sat)
(get-model)
