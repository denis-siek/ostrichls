(declare-const x String)
(declare-const y String)
(assert (= x "MeGMeG"))
(assert (str.in.re x (re.* (re.* (str.to.re "MeG")))))
(check-sat)
(get-model)
