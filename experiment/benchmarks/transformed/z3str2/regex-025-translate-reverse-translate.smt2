(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "'\n'") (re.* (str.to.re "m"))))))
(assert (str.in.re y (re.* (re.++ (str.to.re "'\n'") (re.* (str.to.re "m"))))))
(assert (= (str.len x) (str.len y)))
(assert (not (= x y)))
(assert (= (str.len x) 7))
(check-sat)
(get-model)
