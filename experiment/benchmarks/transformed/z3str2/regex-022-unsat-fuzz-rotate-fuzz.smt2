(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (re.* (str.to.re "")) (str.to.re "")))))
(assert (= (str.len x) 2))
(assert (not (= x "l")))
(assert (not (= x "aT")))
(check-sat)
(get-model)
