(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.union (str.to.re "``QQ||RR") (str.to.re "112233")))))
(assert (= 22 (str.len x)))
(assert (not (= x "``QQ||RR112233``QQ||RR")))
(assert (not (= x "``QQ||RR``QQ||RR112233")))
(check-sat)
(get-model)
