(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "E") (re.+ (str.to.re "}"))))))
(assert (str.in.re y (re.+ (re.++ (str.to.re "a") (re.* (str.to.re "U"))))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.len x) 1))
(check-sat)
(get-model)
