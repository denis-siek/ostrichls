(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re ";") (str.to.re "$")))))
(assert (= 2 (str.len x)))
(assert (not (= x ";;")))
(assert (not (= x ";$")))
(check-sat)
(get-model)
