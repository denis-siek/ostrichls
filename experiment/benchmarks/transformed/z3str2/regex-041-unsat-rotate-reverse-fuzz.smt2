(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (re.+ (str.to.re "d")) (str.to.re "4"))))
(assert (str.in.re x (re.++ (re.* (str.to.re "?")) (str.to.re "c"))))
(assert (str.in.re x (re.union (re.++ (str.to.re """") (str.to.re "")) (re.* (re.* (str.to.re "c"))))))
(check-sat)
(get-model)
