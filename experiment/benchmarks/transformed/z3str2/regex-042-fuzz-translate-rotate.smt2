(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "") (re.+ (str.to.re "8")))))
(assert (str.in.re x (re.++ (re.* (re.* (str.to.re "{"))) (re.union (str.to.re "R") (str.to.re "p")))))
(assert (= 0 (str.len x)))
(check-sat)
(get-model)
