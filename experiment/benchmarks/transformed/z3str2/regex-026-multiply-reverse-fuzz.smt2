(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "i") (re.+ (str.to.re "T,a"))))))
(assert (str.in.re y (re.+ (re.++ (str.to.re "P`") (re.+ (str.to.re "a"))))))
(assert (not (= x y)))
(assert (= (str.len x) (str.to.int y)))
(check-sat)
(get-model)
