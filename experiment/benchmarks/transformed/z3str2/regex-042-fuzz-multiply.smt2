(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "88") (re.+ (str.to.re "")))))
(assert (str.in.re x (re.++ (str.to.re "aa") (re.union (re.* (str.to.re "bb")) (re.* (str.to.re "++"))))))
(assert (= 0 (str.len x)))
(check-sat)
(get-model)
