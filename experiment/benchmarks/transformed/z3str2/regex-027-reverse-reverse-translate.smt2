(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "W")) (str.to.re "x")))))
(assert (= (str.len x) 3))
(assert (not (= x "WWx")))
(assert (not (= x "Wxx")))
(assert (not (= x "xWx")))
(check-sat)
(get-model)
