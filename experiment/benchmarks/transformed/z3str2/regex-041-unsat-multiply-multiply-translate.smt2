(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "\\\\\\\\") (re.* (str.to.re "XXXX")))))
(assert (str.in.re x (re.++ (str.to.re "ssss") (re.* (str.to.re "ssss")))))
(assert (str.in.re x (re.++ (str.to.re "\\\\\\\\") (re.++ (re.* (str.to.re "XXXX")) (re.* (str.to.re "ssss"))))))
(check-sat)
(get-model)
