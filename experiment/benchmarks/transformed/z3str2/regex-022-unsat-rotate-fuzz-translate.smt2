(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (re.+ (str.to.re "")) (str.to.re "")))))
(assert (= (str.to.int x) 4))
(assert (not (= x "W")))
(assert (not (= x "W")))
(check-sat)
(get-model)
