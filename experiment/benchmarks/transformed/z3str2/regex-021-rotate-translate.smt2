(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "P")) (str.to.re "s")))))
(assert (= (str.len x) 2))
(check-sat)
(get-model)
