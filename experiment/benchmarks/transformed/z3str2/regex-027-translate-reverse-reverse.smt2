(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "Y")) (str.to.re "L")))))
(assert (= (str.len x) 3))
(assert (not (= x "YYL")))
(assert (not (= x "YLL")))
(assert (not (= x "LYL")))
(check-sat)
(get-model)
