(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.union (str.to.re "UU") (re.* (str.to.re "..")))))
(assert (str.in.re x (re.union (str.to.re "") (re.+ (str.to.re "UU")))))
(assert (str.in.re x (re.++ (str.to.re "DD") (re.++ (re.+ (str.to.re "")) (re.* (str.to.re "AA"))))))
(check-sat)
(get-model)
