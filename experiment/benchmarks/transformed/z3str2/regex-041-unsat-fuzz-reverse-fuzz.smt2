(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "") (re.* (str.to.re "b")))))
(assert (str.in.re x (re.union (str.to.re "") (re.* (str.to.re "")))))
(assert (str.in.re x (re.union (re.union (re.+ (str.to.re "L")) (re.+ (str.to.re ""))) (str.to.re "v"))))
(check-sat)
(get-model)
