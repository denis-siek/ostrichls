(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "") (str.to.re "2Kj478a")))))
(assert (= 13 (str.to.int x)))
(check-sat)
(get-model)
