(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (re.+ (str.to.re "")) (str.to.re "b"))))
(assert (str.in.re x (re.union (re.+ (str.to.re "5")) (re.+ (re.++ (str.to.re "") (str.to.re "a"))))))
(assert (= 0 (str.len x)))
(check-sat)
(get-model)
