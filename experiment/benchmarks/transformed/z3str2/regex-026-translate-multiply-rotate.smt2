(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "[[")) (str.to.re "ll")))))
(assert (str.in.re y (re.* (re.++ (re.* (str.to.re "[[")) (str.to.re "ll")))))
(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))
(check-sat)
(get-model)
