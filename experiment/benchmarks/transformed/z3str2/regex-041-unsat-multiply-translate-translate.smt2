(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.++ (str.to.re "HH") (re.* (str.to.re "??")))))
(assert (str.in.re x (re.++ (str.to.re "ss") (re.* (str.to.re "ss")))))
(assert (str.in.re x (re.++ (str.to.re "HH") (re.++ (re.* (str.to.re "??")) (re.* (str.to.re "ss"))))))
(check-sat)
(get-model)
