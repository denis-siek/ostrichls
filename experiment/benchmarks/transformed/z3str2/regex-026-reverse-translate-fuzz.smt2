(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "+") (re.+ (str.to.re ""))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "V") (re.+ (str.to.re "|"))))))
(assert (not (= x y)))
(assert (= (str.len x) (str.to.int y)))
(check-sat)
(get-model)
