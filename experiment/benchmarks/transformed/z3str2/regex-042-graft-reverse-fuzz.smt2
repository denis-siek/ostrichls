(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "") (str.to.re "a"))))
(assert (str.in.re x (re.++ (re.union (re.+ (re.* (str.to.re "6"))) (re.+ (str.to.re "b"))) (str.to.re "a"))))
(assert (= (str.len x) 4))
(check-sat)
(get-model)
