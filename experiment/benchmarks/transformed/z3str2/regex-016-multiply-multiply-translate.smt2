(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "AAAAFFFFeeeeJJJJ") (str.to.re "111122223333")))))
(assert (= 44 (str.len x)))
(assert (not (= x "AAAAFFFFeeeeJJJJ111122223333AAAAFFFFeeeeJJJJ")))
(assert (not (= x "AAAAFFFFeeeeJJJJAAAAFFFFeeeeJJJJ111122223333")))
(check-sat)
(get-model)
