(declare-const x String)
(declare-const y String)
(assert (str.in.re x (str.to.re "a")))
(assert (str.in.re y (re.* (str.to.re "fb"))))
(assert (= (str.to.int x) (str.to.int y)))
(assert (= 2 6))
(check-sat)
(get-model)
