(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "P")) (str.to.re "")))))
(assert (= (str.len x) 5))
(assert (not (= x "abh")))
(assert (not (= x "aD")))
(assert (not (= x "V/b")))
(check-sat)
(get-model)
