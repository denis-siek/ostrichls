(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "OO") (str.to.re "rr")))))
(assert (= 4 (str.len x)))
(assert (not (= x "rrrr")))
(assert (not (= x "OOrr")))
(check-sat)
(get-model)
