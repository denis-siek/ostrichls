(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (re.* (str.to.re "bb")) (str.to.re "JR")))))
(assert (= (str.to.int x) 7))
(check-sat)
(get-model)
