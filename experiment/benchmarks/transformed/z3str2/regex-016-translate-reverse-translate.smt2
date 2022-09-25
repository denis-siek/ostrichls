(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "EyXn") (str.to.re "321")))))
(assert (= 11 (str.len x)))
(assert (not (= x "EyXn321EyXn")))
(assert (not (= x "321EyXnEyXn")))
(check-sat)
(get-model)
