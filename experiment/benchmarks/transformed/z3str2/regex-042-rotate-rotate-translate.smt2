(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "F") (re.* (str.to.re "d")))))
(assert (str.in.re x (re.++ (str.to.re "L") (re.* (re.* (re.++ (str.to.re "d") (str.to.re "F")))))))
(assert (= 3 (str.len x)))
(check-sat)
(get-model)
