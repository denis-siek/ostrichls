(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "") (re.+ (str.to.re "K"))))))
(assert (str.in.re y (re.+ (re.union (re.* (str.to.re "%")) (str.to.re "5")))))
(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))
(check-sat)
(get-model)
