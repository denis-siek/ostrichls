(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "bb") (re.* (str.to.re "iQa"))))))
(assert (str.in.re y (re.* (re.union (str.to.re "~P") (re.* (str.to.re "O`"))))))
(assert (not (= x y)))
(assert (= (str.to.int x) (str.len y)))
(check-sat)
(get-model)
