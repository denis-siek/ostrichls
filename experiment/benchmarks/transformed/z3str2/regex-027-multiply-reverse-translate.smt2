(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "''") (re.* (str.to.re "nn"))))))
(assert (= (str.len x) 6))
(assert (not (= x "''nnnn")))
(assert (not (= x "''''nn")))
(assert (not (= x "''nn''")))
(check-sat)
(get-model)
