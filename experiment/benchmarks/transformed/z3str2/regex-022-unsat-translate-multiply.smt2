(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "pp")) (str.to.re "RR")))))
(assert (= (str.len x) 4))
(assert (not (= x "RRRR")))
(assert (not (= x "ppRR")))
(check-sat)
(get-model)
