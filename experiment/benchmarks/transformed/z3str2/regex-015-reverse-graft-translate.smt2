(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.* (str.to.re "21H\\")))))
(assert (str.in.re y (re.* (str.to.re "21H\\"))))
(assert (= 8 4))
(assert (= (str.len y) (str.len x)))
(check-sat)
(get-model)
