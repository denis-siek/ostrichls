(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "b") (re.* (str.to.re "a")))))
(assert (str.in.re x (re.union (re.+ (re.* (str.to.re "p("))) (re.++ (str.to.re "b") (str.to.re "abJ")))))
(assert (= 11 (str.to.int x)))
(check-sat)
(get-model)
