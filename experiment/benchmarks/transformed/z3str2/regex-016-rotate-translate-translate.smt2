(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "FTWJ") (str.to.re "123")))))
(assert (= 11 (str.len x)))
(assert (not (= x "FTWJ123FTWJ")))
(assert (not (= x "FTWJFTWJ123")))
(check-sat)
(get-model)
