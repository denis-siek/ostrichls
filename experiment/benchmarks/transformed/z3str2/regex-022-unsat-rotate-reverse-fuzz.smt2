(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re """") (re.* (str.to.re "b"))))))
(assert (= (str.to.int x) 1))
(assert (not (= x "bb")))
(assert (not (= x "K")))
(check-sat)
(get-model)
