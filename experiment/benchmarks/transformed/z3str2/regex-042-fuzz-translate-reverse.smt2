(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "8") (re.+ (str.to.re "")))))
(assert (str.in.re x (re.++ (re.union (re.* (str.to.re "R")) (re.* (str.to.re "{"))) (str.to.re "p"))))
(assert (= 0 (str.len x)))
(check-sat)
(get-model)
