(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "x"))))
(assert (= (str.len x) 3))
(assert (not (= x "axx")))
(assert (not (= x "xax")))
(assert (not (= x "aax")))
(check-sat)
(get-model)
