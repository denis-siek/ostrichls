(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "m") (re.* (str.to.re "")))))
(assert (str.in.re x (re.union (str.to.re "e") (re.+ (str.to.re "b")))))
(assert (str.in.re x (re.union (re.+ (str.to.re "")) (re.union (str.to.re "a") (re.+ (str.to.re "A"))))))
(check-sat)
(get-model)
