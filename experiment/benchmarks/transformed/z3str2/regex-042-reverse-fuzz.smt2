(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.+ (str.to.re "")) (str.to.re "a"))))
(assert (str.in.re x (re.union (re.++ (re.+ (str.to.re "c")) (re.+ (str.to.re "e"))) (str.to.re "."))))
(assert (= 1 (str.len x)))
(check-sat)
(get-model)
