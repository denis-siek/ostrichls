(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "b") (re.+ (str.to.re "")))))
(assert (str.in.re x (re.++ (str.to.re "c") (re.* (str.to.re "q")))))
(assert (str.in.re x (re.union (re.* (re.* (str.to.re "9"))) (re.union (str.to.re "(") (str.to.re "a")))))
(check-sat)
(get-model)
