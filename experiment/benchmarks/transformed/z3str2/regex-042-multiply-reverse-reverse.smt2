(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "aa") (re.* (str.to.re "bb")))))
(assert (str.in.re x (re.++ (str.to.re "aa") (re.++ (re.* (str.to.re "bb")) (re.* (str.to.re "cc"))))))
(assert (= 6 (str.len x)))
(check-sat)
(get-model)
