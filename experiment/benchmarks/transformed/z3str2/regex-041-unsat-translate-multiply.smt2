(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "//") (re.* (str.to.re "bb")))))
(assert (str.in.re x (re.++ (str.to.re "--") (re.* (str.to.re "--")))))
(assert (str.in.re x (re.++ (str.to.re "//") (re.++ (re.* (str.to.re "bb")) (re.* (str.to.re "--"))))))
(check-sat)
(get-model)
