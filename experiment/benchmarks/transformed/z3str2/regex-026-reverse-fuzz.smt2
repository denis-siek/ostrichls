(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "") (re.+ (str.to.re "a"))))))
(assert (str.in.re y (re.* (re.union (str.to.re "") (re.* (str.to.re "a"))))))
(assert (not (= x y)))
(assert (= (str.to.int x) (str.to.int y)))
(check-sat)
(get-model)
