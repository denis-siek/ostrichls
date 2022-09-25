(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "") (re.+ (str.to.re "f"))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "") (re.* (str.to.re "["))))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.to.int x) 4))
(check-sat)
(get-model)
