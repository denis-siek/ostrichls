(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "Q") (re.* (str.to.re "dOd")))))
(assert (str.in.re x (re.++ (str.to.re "Q") (re.++ (re.* (str.to.re "dOd")) (re.* (str.to.re "|"))))))
(assert (= 3 (str.len x)))
(check-sat)
(get-model)
