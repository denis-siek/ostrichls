(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "aabb"))))
(assert (str.in.re y (str.to.re "aabb")))
(assert (= 8 4))
(assert (= (str.len y) (str.len x)))
(check-sat)
(get-model)
