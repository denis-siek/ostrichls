(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.+ (str.to.re "<")) (str.to.re "")))))
(assert (str.in.re y (re.* (re.union (re.* (str.to.re "<")) (str.to.re "2")))))
(assert (not (= x y)))
(assert (= (str.to.int x) (str.len y)))
(check-sat)
(get-model)
